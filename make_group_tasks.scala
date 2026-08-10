/*
  Generate exercise theories from solution-tagged Isabelle theories.

  Load this file in the Isabelle/jEdit Scala console with

    :load make_group_tasks.scala

  Typical calls:

    Make_Group_Tasks.run()
    Make_Group_Tasks.run(2)
    Make_Group_Tasks.run("4sol_Congruence")
    Make_Group_Tasks.run(1, "4sol_Congruence", (100, 180), 2)

    Make_Group_Tasks.force(1, "4sol_Congruence")
    Make_Group_Tasks.debug()
    Make_Group_Tasks.debug(2, "4sol_Congruence")

  Recognized tags (and only these tags) are:

    %sol  %sol1  %sol2  %sol3
    %solDel  %sol1Del  %sol2Del  %sol3Del

  A ROOT alias has the strict form

    "Source_Theory" (* target = "Target_Theory" *)
*/

import isabelle._
import isabelle.jedit.PIDE
import org.gjt.sp.jedit.jEdit

import java.io.{File => JFile}
import java.nio.file.{Files, StandardCopyOption}
import java.util.regex.Matcher
import scala.collection.mutable
import scala.util.matching.Regex


object Make_Group_Tasks {
  final case class Line_Override(from: Int, to: Int, level: Int) {
    def contains(line: Int): Boolean = from <= line && line <= to
  }

  final case class Config(
    level: Int = 1,
    theory: Option[String] = None,
    line_override: Option[Line_Override] = None
  )

  final case class Task_Error(file: String, line: Int, message: String)

  final case class Run_Result(
    checked: List[JFile],
    written: List[JFile],
    errors: List[Task_Error]
  ) {
    def ok: Boolean = errors.isEmpty
  }

  private sealed trait Mode { def writes: Boolean; def force: Boolean }
  private case object Run_Mode extends Mode { val writes = true; val force = false }
  private case object Force_Mode extends Mode { val writes = true; val force = true }
  private case object Debug_Mode extends Mode { val writes = false; val force = false }

  private sealed trait Disposition
  private case object Replace_With_Sorry extends Disposition
  private case object Delete extends Disposition

  private final case class Solution_Tag(
    spelling: String,
    direct_level: Option[Int],
    disposition: Disposition
  )

  private final case class Tag_Occurrence(tag: Solution_Tag, start: Int, end: Int)

  private final class Span_Info(
    val index: Int,
    val span: Command_Span.Span,
    val start: Int,
    val end: Int,
    val start_line: Int,
    val tags: List[Tag_Occurrence]
  ) {
    var region_end: Int = index
    var level: Int = 0
    var disposition: Option[Disposition] = None

    def name: String = span.name
    def keyword_kind: Option[String] = span.kind.keyword_kind
    def explicit_tag: Option[Solution_Tag] = tags.headOption.map(_.tag)
  }

  private final case class Edit(
    start: Int,
    end: Int,
    text: String,
    source_line: Int
  )

  private final case class Generated(text: String, source_lines: Vector[Int]) {
    def source_line(generated_line: Int): Int = {
      if (source_lines.isEmpty) 1
      else source_lines(math.max(0, math.min(source_lines.length - 1, generated_line - 1)))
    }
  }

  private final case class Theory_Spec(
    entry: String,
    source: JFile,
    source_base: String,
    target_base: String
  )

  private final case class Session_Context(
    info: Sessions.Info,
    root_file: JFile,
    theories: List[Theory_Spec],
    aliases: Map[String, String],
    syntax: Outer_Syntax,
    validation_logic: String
  )

  private final case class Candidate(spec: Theory_Spec, target: JFile, generated: Generated)
  private final case class Validation(ok: Boolean, generated_line: Option[Int], details: String)

  private final case class Task_Failure(problem: Task_Error)
    extends RuntimeException(problem.file + ":" + problem.line + ": " + problem.message)

  private final class Capture_Progress extends Progress {
    private val buffer = new mutable.ListBuffer[String]

    override def output(messages: Progress.Output): Unit = synchronized {
      for (message <- messages if do_output(message)) buffer += message.message.text
    }

    def text: String = synchronized { buffer.mkString("\n") }
  }


  private val Declared_Theory: Regex =
    """(?m)^(\s*theory\s+)(?:\"([^\"]+)\"|(\S+))""".r

  private val Header_Imports: Regex = """(?s)(\bimports\b)(.*?)(\bbegin\b)""".r

  private val Target_Comment: Regex =
    """(?s)(?:\"([^\"]+)\"|([A-Za-z0-9_./'\-]+))\s*\(\*\s*target\s*=\s*\"([^\"]+)\"\s*\*\)""".r

  private val Any_Target_Comment: Regex = """(?s)\(\*\s*target\b.*?\*\)""".r

  private val Validation_Position: Regex =
    """(?m)([^\s:\r\n]+\.thy):(\d+)(?::\d+)?""".r

  private val At_Command_Position: Regex =
    """(?m)At command [^\r\n]*\(line\s+(\d+)\s+of\s+\"([^\"]+\.thy)\"\)""".r

  private val Failure_Position: Regex =
    """(?m)^\*\*\* [^\r\n]*\(line\s+(\d+)\s+of\s+\"([^\"]+\.thy)\"\)""".r

  private val Error_Markup_Position: Regex =
    """(?s)Error.{0,120}?line=(\d+).{0,240}?file=([^\u0005\u0006\r\n]+\.thy)""".r

  private val Managed_Theories_Block: Regex =
    """(?ms)^\s*theories\s*$\s*(.*?)(?=^\s*[A-Za-z_]+(?:\s|$)|\z)""".r

  private val Managed_Theory_Line: Regex = """(?m)^\s*\"([^\"]+)\"\s*$""".r

  private val Cartouche_Close = "\\<close>"
  private val File_Antiquotation_Open = "\\<^file>\\<open>"


  private def file_error(file: JFile, line: Int, message: String): Nothing =
    throw Task_Failure(Task_Error(file.getCanonicalPath, line, message))

  private def line_number(source: String, offset: Int): Int =
    1 + source.substring(0, math.max(0, math.min(offset, source.length))).count(_ == '\n')

  private def normalize_theory_argument(s: String): String =
    Library.try_unsuffix(".thy", s.trim).getOrElse(s.trim)

  private def canonical(file: JFile): JFile = file.getCanonicalFile

  private def same_file(a: JFile, b: JFile): Boolean = canonical(a) == canonical(b)


  /* Session and ROOT information */

  private def validate_target_name(root: JFile, target: String): String = {
    val legal_chars = target.matches("[A-Za-z0-9_.'-]+")
    if (!legal_chars || !Url.is_base_name(target) || target == "." || target == ".." ||
        target.endsWith(".thy")) {
      file_error(root, 1,
        "Bad target theory name " + quote(target) +
          "; expected a basename without .thy")
    }
    target
  }

  private def root_aliases(root: JFile): Map[String, String] = {
    val source = File.read(root)
    val matches = Target_Comment.findAllMatchIn(source).toList
    val accepted_ranges = matches.map(m => m.start -> m.end)

    for (item <- Any_Target_Comment.findAllMatchIn(source)) {
      if (!accepted_ranges.exists { case (a, b) => a <= item.start && item.end <= b }) {
        file_error(root, line_number(source, item.start),
          "Malformed target comment; expected (* target = \"Target_Theory\" *) " +
            "immediately after a theory name")
      }
    }

    val pairs = matches.map { item =>
      val source_name = Option(item.group(1)).getOrElse(item.group(2))
      source_name -> validate_target_name(root, item.group(3))
    }
    val duplicates = Library.duplicates(pairs.map(_._1))
    if (duplicates.nonEmpty)
      file_error(root, 1, "Duplicate target comments for " + commas_quote(duplicates))
    pairs.toMap
  }

  private def local_session_info(
    structure: Sessions.Structure,
    cwd: JFile
  ): Sessions.Info = {
    val active_name =
      try { PIDE.resources.session_base.session_name }
      catch { case _: Throwable => "" }
    val active = structure.get(active_name).filter(info => same_file(info.dir.file, cwd))
    active.getOrElse {
      val local = structure.imports_graph.keys_iterator
        .map(structure(_))
        .filter(info => same_file(info.dir.file, cwd))
        .toList
      local match {
        case List(info) => info
        case Nil =>
          error("No Isabelle session rooted at " + quote(cwd.getCanonicalPath))
        case infos =>
          error("More than one Isabelle session is rooted at " +
            quote(cwd.getCanonicalPath) + ": " + commas_quote(infos.map(_.name)))
      }
    }
  }

  private def session_context(cwd: JFile): Session_Context = {
    val options = Options.init()
    val structure = Sessions.load_structure(options, dirs = List(File.path(cwd)))
    val info = local_session_info(structure, cwd)
    val root = (info.dir + Path.basic("ROOT")).file
    val aliases0 = root_aliases(root)

    val entries = info.theories.flatMap(_._2.map(_._1))
    val theories = entries.map { entry0 =>
      val entry = Library.try_unsuffix(".thy", entry0).getOrElse(entry0)
      val path = Path.explode(entry)
      val source = (info.dir + path.thy).file
      val base = path.file_name
      val alias = aliases0.get(entry).orElse(aliases0.get(base)).getOrElse(base)
      Theory_Spec(entry, source, base, alias)
    }

    val missing = theories.filterNot(_.source.isFile)
    if (missing.nonEmpty)
      error("Missing theory file(s) listed directly in session " + quote(info.name) + ":\n" +
        cat_lines(missing.map(item => "  " + item.source.getPath)))

    val duplicate_targets = Library.duplicates(theories.map(_.target_base))
    if (duplicate_targets.nonEmpty)
      error("Duplicate generated theory name(s): " + commas_quote(duplicate_targets))

    val aliases = theories.flatMap { item =>
      List(item.entry -> item.target_base, item.source_base -> item.target_base)
    }.toMap
    val live_base =
      try {
        val base = PIDE.resources.session_base
        if (base.session_name == info.name) Some(base) else None
      }
      catch { case _: Throwable => None }
    val syntax = live_base.map(_.overall_syntax).getOrElse {
      val selected_structure =
        structure.selection(Sessions.Selection(sessions = List(info.name)))
      Sessions.deps(selected_structure).check_errors(info.name).overall_syntax
    }
    val validation_logic = live_base.map(_.session_name).getOrElse {
      info.imports.lastOption.orElse(info.parent)
        .getOrElse(error("No validation logic available for session " + quote(info.name)))
    }
    Session_Context(info, root, theories, aliases, syntax, validation_logic)
  }

  private def select_theories(context: Session_Context, requested: Option[String]): List[Theory_Spec] =
    requested.map(normalize_theory_argument) match {
      case None => context.theories
      case Some(name) if name.nonEmpty =>
        val matching = context.theories.filter(item => item.entry == name || item.source_base == name)
        matching match {
          case List(item) => List(item)
          case Nil =>
            error(quote(name + ".thy") + " is not listed directly under theories in session " +
              quote(context.info.name))
          case _ => error("Ambiguous theory name " + quote(name))
        }
      case Some(_) => error("Empty theory name")
    }


  /* Tags and command regions */

  private def solution_tag(name: String): Option[Solution_Tag] = name match {
    case "sol" => Some(Solution_Tag(name, None, Replace_With_Sorry))
    case "sol1" => Some(Solution_Tag(name, Some(1), Replace_With_Sorry))
    case "sol2" => Some(Solution_Tag(name, Some(2), Replace_With_Sorry))
    case "sol3" => Some(Solution_Tag(name, Some(3), Replace_With_Sorry))
    case "solDel" => Some(Solution_Tag(name, None, Delete))
    case "sol1Del" => Some(Solution_Tag(name, Some(1), Delete))
    case "sol2Del" => Some(Solution_Tag(name, Some(2), Delete))
    case "sol3Del" => Some(Solution_Tag(name, Some(3), Delete))
    case _ => None
  }

  private def span_tags(span: Command_Span.Span, span_start: Int): List[Tag_Occurrence] = {
    val offsets = new Array[Int](span.content.length)
    var offset = span_start
    for ((token, i) <- span.content.zipWithIndex) {
      offsets(i) = offset
      offset += token.source.length
    }

    val proper = span.content.zipWithIndex.filterNot(_._1.is_ignored)
    proper.sliding(2).flatMap {
      case List((percent, percent_i), (name, name_i))
          if percent.is_keyword && percent.source == "%" && name.is_name =>
        solution_tag(name.source).map(tag =>
          Tag_Occurrence(tag, offsets(percent_i), offsets(name_i) + name.source.length))
      case _ => None
    }.toList
  }

  private def parse_spans(
    syntax: Outer_Syntax,
    source: String,
    file: JFile
  ): List[Span_Info] = {
    val result = new mutable.ListBuffer[Span_Info]
    var offset = 0
    for ((span, index) <- syntax.parse_spans(source).zipWithIndex) {
      val end = offset + span.length
      val tags = span_tags(span, offset)
      val distinct = tags.map(_.tag).distinct
      if (distinct.lengthCompare(1) > 0) {
        file_error(file, line_number(source, offset),
          "Conflicting solution tags on command " + quote(span.name) + ": " +
            commas_quote(distinct.map(_.spelling)))
      }
      result += new Span_Info(index, span, offset, end, line_number(source, offset), tags)
      offset = end
    }
    result.toList
  }

  private def set_regions(spans: List[Span_Info]): Unit = {
    val goals = new mutable.Stack[Int]
    val proofs = new mutable.Stack[Int]
    val contexts = new mutable.Stack[Int]

    def kind(item: Span_Info): String = item.keyword_kind.getOrElse("")
    def close(stack: mutable.Stack[Int], at: Int): Unit =
      if (stack.nonEmpty) spans(stack.pop()).region_end = at

    for (item <- spans if item.name.nonEmpty) {
      val k = kind(item)

      if (Keyword.theory_goal(k) || Keyword.proof_goal(k)) goals.push(item.index)
      if (k == Keyword.PRF_BLOCK) proofs.push(item.index)
      if (k == Keyword.PRF_OPEN) contexts.push(item.index)

      if (k == Keyword.QED_BLOCK) {
        close(proofs, item.index)
        close(goals, item.index)
      }
      else if (Keyword.qed(k) || Keyword.qed_global(k)) close(goals, item.index)

      if (k == Keyword.PRF_CLOSE) close(contexts, item.index)
    }
  }

  private final case class Active_Region(end: Int, level: Int, disposition: Disposition)

  /* A command may own a range for deletion without introducing a new level
     scope.  Theory goals (lemma/theorem/...) propagate their level through
     their proof, and an explicitly tagged proof/context block can raise it
     again.  Proof-local goals such as hence/show own their terminating proof
     command for deletion, but do not introduce another propagation level. */
  private def propagates_level(item: Span_Info): Boolean =
    item.keyword_kind.exists(kind =>
      Keyword.theory_goal(kind) || kind == Keyword.PRF_BLOCK || kind == Keyword.PRF_OPEN)

  private def assign_levels(spans: List[Span_Info]): Unit = {
    var active: List[Active_Region] = Nil

    for (item <- spans) {
      active = active.filter(_.end >= item.index)
      val inherited_level = active.headOption.map(_.level).getOrElse(0)
      val inherited_disposition = active.headOption.map(_.disposition)

      item.explicit_tag match {
        case Some(tag) =>
          item.level = tag.direct_level.getOrElse(math.min(3, inherited_level + 1))
          item.disposition = Some(tag.disposition)
          if (item.region_end > item.index && propagates_level(item))
            active = Active_Region(item.region_end, item.level, tag.disposition) :: active
        case None =>
          item.level = inherited_level
          item.disposition = inherited_disposition
      }
    }
  }


  /* Text transformation */

  private def threshold(config: Config, line: Int): Int =
    config.line_override.filter(_.contains(line)).map(_.level).getOrElse(config.level)

  private def destructive_edits(
    spans: List[Span_Info],
    config: Config
  ): List[Edit] = {
    val edits = new mutable.ListBuffer[Edit]
    var covered_until = -1

    for (item <- spans if item.name.nonEmpty) {
      val selected = item.level >= threshold(config, item.start_line)
      if (selected && item.disposition.isDefined && item.start >= covered_until) {
        val disposition = item.disposition.get
        val proof_region = item.name == "proof" && item.region_end > item.index
        /* Isabelle's . and .. are terminal proof commands (short forms of
           finishing from the current facts), so tagged occurrences have the
           same replacement behavior as by/done. */
        val terminal = Set("by", "done", ".", "..").contains(item.name)
        val region_end = if (terminal) item.index else item.region_end
        val end = spans(region_end).end
        val replacement =
          if (disposition == Replace_With_Sorry && (terminal || proof_region)) "sorry"
          else ""

        edits += Edit(item.start, end, replacement, item.start_line)
        covered_until = end
      }
    }
    edits.toList
  }

  private def tag_removal_edits(
    spans: List[Span_Info],
    destructive: List[Edit]
  ): List[Edit] = {
    def covered(start: Int, end: Int): Boolean =
      destructive.exists(edit => edit.start <= start && end <= edit.end)

    for {
      item <- spans
      occurrence <- item.tags
      if !covered(occurrence.start, occurrence.end)
    } yield Edit(occurrence.start, occurrence.end, "", item.start_line)
  }

  private def apply_edits(source: String, edits0: List[Edit], file: JFile): Generated = {
    val edits = edits0.sortBy(edit => (edit.start, edit.end))
    for ((left, right) <- edits.zip(edits.drop(1)) if left.end > right.start)
      file_error(file, line_number(source, right.start), "Overlapping generated edits")

    val output = new StringBuilder(source.length)
    val line_map = new mutable.ListBuffer[Int]
    line_map += 1
    var source_line = 1
    var cursor = 0

    def append_source(text: String): Unit = {
      for (c <- text) {
        output += c
        if (c == '\n') {
          source_line += 1
          line_map += source_line
        }
      }
    }

    def skip_source(text: String): Unit =
      source_line += text.count(_ == '\n')

    def append_replacement(text: String, origin: Int): Unit = {
      for (c <- text) {
        output += c
        if (c == '\n') line_map += origin
      }
    }

    for (edit <- edits) {
      append_source(source.substring(cursor, edit.start))
      append_replacement(edit.text, edit.source_line)
      skip_source(source.substring(edit.start, edit.end))
      cursor = edit.end
    }
    append_source(source.substring(cursor))
    Generated(output.toString, line_map.toVector)
  }

  private def declared_name(source: String): Option[String] =
    Declared_Theory.findFirstMatchIn(source).map(item =>
      Option(item.group(2)).getOrElse(item.group(3)))

  private def rewrite_declared_name(source: String, target: String): String =
    Declared_Theory.findFirstMatchIn(source) match {
      case None => error("Missing theory header")
      case Some(item) =>
        source.substring(0, item.start) + item.group(1) + quote(target) +
          source.substring(item.end)
    }

  private def replace_import(imports: String, old_name: String, new_name: String): String = {
    if (old_name == new_name) imports
    else {
      val boundary = "A-Za-z0-9_.'-"
      val pattern = ("(?<![" + boundary + "])" + Regex.quote(old_name) +
        "(?![" + boundary + "])").r
      pattern.replaceAllIn(imports, Matcher.quoteReplacement(new_name))
    }
  }

  private def rewrite_header(source: String, target: String, aliases: Map[String, String]): String = {
    val renamed = rewrite_declared_name(source, target)
    Header_Imports.findFirstMatchIn(renamed) match {
      case None => renamed
      case Some(item) =>
        val imports0 = item.group(2)
        val imports = aliases.toList.sortBy { case (old_name, _) => -old_name.length }
          .foldLeft(imports0) { case (text, (old_name, new_name)) =>
            replace_import(text, old_name, new_name)
          }
        renamed.substring(0, item.start(2)) + imports + renamed.substring(item.end(2))
    }
  }

  private def transform(
    context_syntax: Outer_Syntax,
    source: String,
    file: JFile,
    target: String,
    aliases: Map[String, String],
    config: Config
  ): Generated = {
    val spans = parse_spans(context_syntax, source, file)
    set_regions(spans)
    assign_levels(spans)
    val destructive = destructive_edits(spans, config)
    val tag_removals = tag_removal_edits(spans, destructive)
    val generated = apply_edits(source, destructive ::: tag_removals, file)
    generated.copy(text = rewrite_header(generated.text, target, aliases))
  }


  /* group_tasks/ROOT */

  private def group_session_name(info: Sessions.Info): String = info.name + "_Group_Tasks"

  private def existing_group_entries(root: JFile): List[String] = {
    if (!root.isFile) Nil
    else {
      val source = File.read(root)
      Managed_Theories_Block.findFirstMatchIn(source).toList.flatMap { block =>
        Managed_Theory_Line.findAllMatchIn(block.group(1)).map(_.group(1)).toList
      }
    }
  }

  private def render_group_root(info: Sessions.Info, entries: List[String]): String = {
    val parent = info.parent.getOrElse(error("Current session has no parent session"))
    val sessions =
      if (info.imports.isEmpty) ""
      else "  sessions\n" + info.imports.map(name => "    " + quote(name)).mkString("\n") + "\n"
    "session " + quote(group_session_name(info)) + " = " + quote(parent) + " +\n" +
      "  options [quick_and_dirty, document = false]\n" + sessions +
      "  theories\n" + entries.distinct.map(name => "    " + quote(name)).mkString("\n") + "\n"
  }

  private def add_group_entry(
    info: Sessions.Info,
    output_dir: JFile,
    target: String
  ): String = {
    val root = new JFile(output_dir, "ROOT")
    val entries = existing_group_entries(root)
    render_group_root(info, if (entries.contains(target)) entries else entries :+ target)
  }


  /* Isabelle validation */

  private def files_in(dir: JFile): List[JFile] =
    Option(dir.listFiles()).fold(List.empty[JFile])(_.toList)

  private def file_references(source: String): List[String] = {
    val result = new mutable.ListBuffer[String]
    var opening = source.indexOf(File_Antiquotation_Open)
    while (opening >= 0) {
      val body_start = opening + File_Antiquotation_Open.length
      val closing = source.indexOf(Cartouche_Close, body_start)
      if (closing < 0) opening = -1
      else {
        result += source.substring(body_start, closing)
        opening = source.indexOf(File_Antiquotation_Open, closing + Cartouche_Close.length)
      }
    }
    result.toList.distinct
  }

  private def stage_document_files(stage: Path, cwd: JFile, text: String): Unit = {
    val stage_root = stage.file.getCanonicalFile
    for {
      reference <- file_references(text)
      if reference.nonEmpty
      if !reference.startsWith("~~") && !reference.startsWith("$")
      if !new JFile(reference).isAbsolute
      target = new JFile(stage_root, reference).getCanonicalFile
      if target.toPath.startsWith(stage_root.toPath)
    } {
      val source = new JFile(cwd, reference)
      Option(target.getParentFile).foreach(parent => Files.createDirectories(parent.toPath))
      if (source.isFile)
        Files.copy(source.toPath, target.toPath, StandardCopyOption.REPLACE_EXISTING)
      else if (!reference.endsWith(".thy"))
        Files.write(target.toPath, Array.emptyByteArray)
    }
  }

  private def first_generated_line(details: String, target_name: String): Option[Int] = {
    def target(path: String): Boolean = new JFile(path).getName == target_name

    At_Command_Position.findAllMatchIn(details).collectFirst {
      case item if target(item.group(2)) => item.group(1).toInt
    }.orElse {
      Failure_Position.findAllMatchIn(details).collectFirst {
        case item if target(item.group(2)) => item.group(1).toInt
      }
    }.orElse {
      Error_Markup_Position.findAllMatchIn(details).collectFirst {
        case item if target(item.group(2)) => item.group(1).toInt
      }
    }.orElse {
      Validation_Position.findAllMatchIn(details).collectFirst {
        case item if target(item.group(1)) => item.group(2).toInt
      }
    }
  }

  private def on_isabelle_thread[A](body: => A): A =
    if (Isabelle_Thread.check_self) body
    else Future.thread[A](name = "make_group_tasks") { body }.join

  private def validate(
    candidate: Candidate,
    context: Session_Context,
    cwd: JFile,
    output_dir: JFile
  ): Validation = {
    Isabelle_System.with_tmp_dir("group_tasks_check") { stage =>
      for (file <- files_in(output_dir) if file.isFile && file.getName.endsWith(".thy"))
        Isabelle_System.copy_file(file, (stage + Path.basic(file.getName)).file)

      /* The active session already contains every direct source theory.  Use a
         fresh checking name, so validation also works when no target alias was
         specified and the generated basename equals the source basename. */
      val checking_base =
        if (candidate.spec.target_base != candidate.spec.source_base)
          candidate.spec.target_base
        else "Group_Tasks_Check_" + java.lang.Long.toUnsignedString(System.nanoTime())
      val checking_name = checking_base + ".thy"
      val checking_text = rewrite_declared_name(candidate.generated.text, checking_base)
      File.write(stage + Path.basic(checking_name), checking_text)
      stage_document_files(stage, cwd, candidate.generated.text)

      val progress = new Capture_Progress
      try {
        val results = on_isabelle_thread {
          Process_Theories.process_theories(
            options = context.info.options,
            logic = context.validation_logic,
            directory = Some(stage),
            theories = List(checking_base),
            output_messages = true,
            progress = progress)
        }
        val process = results(Sessions.DRAFT)
        val process_details = cat_lines(List(process.out, process.err).filter(_.nonEmpty))
        val details = cat_lines(List(progress.text, process_details).filter(_.nonEmpty))
        Validation(results.ok,
          if (results.ok) None else first_generated_line(details, checking_name),
          if (details.nonEmpty) details else if (results.ok) "" else "Isabelle build failed")
      }
      catch {
        case exn: Throwable if !Exn.is_interrupt(exn) =>
          val details = Exn.message(exn) + if_proper(progress.text, "\n" + progress.text)
          Validation(false, first_generated_line(details, checking_name), details)
      }
    }
  }


  /* Atomic persistent writes */

  private def atomic_write(file: JFile, text: String): Unit = {
    val parent = file.getCanonicalFile.getParentFile
    Files.createDirectories(parent.toPath)
    val temporary = Files.createTempFile(parent.toPath, file.getName + ".", ".new").toFile
    try {
      File.write(File.path(temporary), text)
      try {
        Files.move(temporary.toPath, file.toPath,
          StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
      }
      catch {
        case _: java.nio.file.AtomicMoveNotSupportedException =>
          Files.move(temporary.toPath, file.toPath, StandardCopyOption.REPLACE_EXISTING)
      }
    }
    finally { Files.deleteIfExists(temporary.toPath) }
  }

  private def write_candidate(
    candidate: Candidate,
    context: Session_Context,
    output_dir: JFile
  ): Unit = {
    atomic_write(candidate.target, candidate.generated.text)
    val root_text = add_group_entry(context.info, output_dir, candidate.spec.target_base)
    atomic_write(new JFile(output_dir, "ROOT"), root_text)
  }


  /* Execution and jEdit navigation */

  private def validate_config(config: Config): Unit = {
    require(0 <= config.level && config.level <= 3,
      "The replacement level must be between 0 and 3")
    config.line_override.foreach { item =>
      require(item.from >= 1, "The first line number must be positive")
      require(item.to >= item.from, "The interval end must not precede its start")
      require(0 <= item.level && item.level <= 3,
        "The interval replacement level must be between 0 and 3")
    }
  }

  private def execute(config: Config, mode: Mode): Run_Result = {
    validate_config(config)
    val cwd = new JFile(".").getCanonicalFile
    val context = session_context(cwd)
    val selected = select_theories(context, config.theory)
    val output_dir = new JFile(cwd, "group_tasks")
    if (mode.writes) Files.createDirectories(output_dir.toPath)

    val checked = new mutable.ListBuffer[JFile]
    val written = new mutable.ListBuffer[JFile]
    val errors = new mutable.ListBuffer[Task_Error]

    for (spec <- selected if errors.isEmpty || mode != Debug_Mode) {
      checked += spec.source
      println("Checking " + spec.source.getName + " at level " + config.level + " ...")

      val candidate =
        try {
          val generated = transform(
            context.syntax, File.read(spec.source), spec.source,
            spec.target_base, context.aliases, config)
          Candidate(spec, new JFile(output_dir, spec.target_base + ".thy"), generated)
        }
        catch {
          case Task_Failure(problem) =>
            errors += problem
            println(problem.file + ":" + problem.line + ": " + problem.message)
            null
        }

      if (candidate != null) {
        val validation = validate(candidate, context, cwd, output_dir)
        if (!validation.ok) {
          val source_line = validation.generated_line.map(candidate.generated.source_line).getOrElse(-1)
          val problem = Task_Error(spec.source.getCanonicalPath, source_line,
            "Isabelle validation failed" + if_proper(validation.details, ":\n" + validation.details))
          errors += problem
          val position = if (source_line > 0) ":" + source_line else ""
          println(spec.source.getName + position + ": Isabelle validation failed")
          if (validation.details.nonEmpty) println(validation.details)
        }

        if (mode.writes && (validation.ok || mode.force)) {
          write_candidate(candidate, context, output_dir)
          written += candidate.target
          println("Wrote " + candidate.target.getPath +
            if_proper(!validation.ok, " (forced despite validation errors)"))
        }
        else if (validation.ok) println(spec.source.getName + ": no mistakes found")
      }
    }
    Run_Result(checked.toList, written.toList, errors.toList)
  }

  private def open_first_error(result: Run_Result): Unit =
    result.errors.headOption.foreach { problem =>
      val position = if (problem.line > 0) ":" + problem.line else ""
      println("Opening " + problem.file + position)
      GUI_Thread.later {
        val view = jEdit.getActiveView()
        if (view == null) println("Cannot navigate: jEdit has no active view")
        else {
          val line = if (problem.line > 0) problem.line - 1 else -1
          PIDE.editor.goto_file(view, problem.file, line = line, focus = true)
          view.requestFocus()
        }
      }
    }

  private def make_config(
    level: Int,
    theory: String,
    lines: Option[(Int, Int)],
    override_level: Option[Int]
  ): Config = {
    val line_override = for {
      (from, to) <- lines
      m <- override_level
    } yield Line_Override(from, to, m)
    Config(level, Option(theory).map(_.trim).filter(_.nonEmpty), line_override)
  }


  def run(): Unit = { execute(Config(), Run_Mode); () }
  def run(level: Int): Unit = { execute(Config(level = level), Run_Mode); () }
  def run(theory: String): Unit = { execute(Config(theory = Some(theory)), Run_Mode); () }
  def run(level: Int, theory: String): Unit =
    { execute(make_config(level, theory, None, None), Run_Mode); () }
  def run(lines: (Int, Int), m: Int): Unit =
    { execute(Config(line_override = Some(Line_Override(lines._1, lines._2, m))), Run_Mode); () }
  def run(level: Int, lines: (Int, Int), m: Int): Unit =
    { execute(Config(level = level,
        line_override = Some(Line_Override(lines._1, lines._2, m))), Run_Mode); () }
  def run(theory: String, lines: (Int, Int), m: Int): Unit =
    { execute(make_config(1, theory, Some(lines), Some(m)), Run_Mode); () }
  def run(level: Int, theory: String, lines: (Int, Int), m: Int): Unit =
    { execute(make_config(level, theory, Some(lines), Some(m)), Run_Mode); () }
  def run(config: Config): Unit = { execute(config, Run_Mode); () }

  def force(): Unit = { execute(Config(), Force_Mode); () }
  def force(level: Int): Unit = { execute(Config(level = level), Force_Mode); () }
  def force(theory: String): Unit = { execute(Config(theory = Some(theory)), Force_Mode); () }
  def force(level: Int, theory: String): Unit =
    { execute(make_config(level, theory, None, None), Force_Mode); () }
  def force(lines: (Int, Int), m: Int): Unit =
    { execute(Config(line_override = Some(Line_Override(lines._1, lines._2, m))), Force_Mode); () }
  def force(level: Int, lines: (Int, Int), m: Int): Unit =
    { execute(Config(level = level,
        line_override = Some(Line_Override(lines._1, lines._2, m))), Force_Mode); () }
  def force(theory: String, lines: (Int, Int), m: Int): Unit =
    { execute(make_config(1, theory, Some(lines), Some(m)), Force_Mode); () }
  def force(level: Int, theory: String, lines: (Int, Int), m: Int): Unit =
    { execute(make_config(level, theory, Some(lines), Some(m)), Force_Mode); () }
  def force(config: Config): Unit = { execute(config, Force_Mode); () }

  private def debug_all(
    theory: Option[String],
    line_override: Option[Line_Override]
  ): Unit = {
    var level = 1
    var finished = false
    while (level <= 3 && !finished) {
      val result = execute(Config(level = level, theory = theory,
        line_override = line_override), Debug_Mode)
      if (!result.ok) { open_first_error(result); finished = true }
      level += 1
    }
    if (!finished) println("No mistakes found at levels 1, 2, or 3")
  }

  def debug(): Unit = debug_all(None, None)
  def debug(level: Int): Unit = open_first_error(execute(Config(level = level), Debug_Mode))
  def debug(theory: String): Unit = debug_all(Some(theory), None)
  def debug(lines: (Int, Int), m: Int): Unit =
    debug_all(None, Some(Line_Override(lines._1, lines._2, m)))
  def debug(theory: String, lines: (Int, Int), m: Int): Unit =
    debug_all(Some(theory), Some(Line_Override(lines._1, lines._2, m)))
  def debug(level: Int, lines: (Int, Int), m: Int): Unit =
    open_first_error(execute(Config(level = level,
      line_override = Some(Line_Override(lines._1, lines._2, m))), Debug_Mode))
  def debug(level: Int, theory: String): Unit =
    open_first_error(execute(make_config(level, theory, None, None), Debug_Mode))
  def debug(level: Int, theory: String, lines: (Int, Int), m: Int): Unit =
    open_first_error(execute(make_config(level, theory, Some(lines), Some(m)), Debug_Mode))
  def debug(config: Config): Unit = open_first_error(execute(config, Debug_Mode))
}
