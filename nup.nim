
#
#
# TODO:
# - [ ] try out 

import
  std/[macros, tables, os, re, pegs, sequtils, terminal],
  pkg/[ast_pattern_matching, procs, yaml, mustache, nimgraphviz,
       zero_functional, itertools, trees/avl]
from pkg/globby import globMatch
export os, avl #, procs, zero_functional

type Iterable[T] = concept c
  c.items() is T

template build(targets: Iterable[string], cmds) =
  for target {.inject.} in targets:
    cmds

template build(targets: Iterable[string], deps: Iterable[string], cmds) =
  for target {.inject.} in targets:
    cmds


type
  NodeKind* {.pure.} = enum
    File
    Cmd
    Dir
    Var
    GenFile
    Ghost
    Group
    GenDir
    Root
  FlagsKind* {.pure.} = enum
    None
    Modify
    Create
    Config
    Variant
    Transient
  LinkKind* {.pure.} = enum
    Normal
    Sticky
    Group
  # FileNode* = object
  #   modTime*: int64
  #   path*: string

  # Dag* = object
  #   nodes*: seq[FileNode]

type
  Patterns* = object
    lits*: seq[string]
    globs*: seq[string]
    res*: seq[string]
    pegs*: seq[string]
  PathPatterns* = object
    incls*: Patterns
    excls*: Patterns

var tree = [
  "a",
  "b"
]

var rules = {
  "c": ["a"],
  "d": ["b"],
}.toTable

# proc inputFileChangeList*(inputs: openArray[string], changeList: var seq[string]) =
#   for fileChanged in inputs:
#     changeList.add fileChanged

# proc buildPartialDag*(dag: var Dag, changeList: openArray[string]) =
#   for fileChanged in changeList:
#     dag.add fileChanged

# proc link*(dag: var Dag, node, dep: FileNode) =
#   ## Add a link from a node to its dependency.

# proc deps*(file: FileNode): seq[FileNode] =
#   ## Return the dependencies of `file`.

# proc add*(dag: var Dag, node: FileNode) =
#   dag.nodes.add node
#   for dep in node.deps:
#     if dep noint dag:
#       dag.add dep
#       dag.link node, dep



# template build(targets: (iterator(): string {.closure.}), deps: (iterator(): string {.closure.})) =
#   for target in targets:
#     echo "building " & target

proc diag(msg: string) =
  styledWriteLine(stderr, fgYellow, msg)

type InputNodes = object
  pats: NimNode
  inclCalls, exclCalls: seq[NimNode]
  inclBins, exclBins: seq[NimNode]

func newInputNodes: InputNodes =
  result.pats = quote do:
    PathPatterns(incls: Patterns(lits: @[], globs: @[], res: @[], pegs: @[]),
                 excls: Patterns(lits: @[], globs: @[], res: @[], pegs: @[]))
func addLit(patConstr: var NimNode, val: NimNode, isExcl = false) =
  patConstr[isExcl.ord + 1][1][1][1][1].add val
func addGlob(patConstr: var NimNode, val: NimNode, isExcl = false) =
  patConstr[isExcl.ord + 1][1][2][1][1].add val
func addRe(patConstr: var NimNode, val: NimNode, isExcl = false) =
  patConstr[isExcl.ord + 1][1][3][1][1].add val
func addPeg(patConstr: var NimNode, val: NimNode, isExcl = false) =
  patConstr[isExcl.ord + 1][1][4][1][1].add val

func extractCmds(node: NimNode): NimNode =
  var firstStmtListIdx = 0
  for idx in countdown(node.len-2, 0, 1):
    if node[idx].kind != nnkStmtList:
      firstStmtListIdx = idx + 1
      break
  # doAssert firstStmtListIdx != 0
  if firstStmtListIdx != node.len-1:
    error("`do:` command lists aren't supported yet")
  result = copy node[firstStmtListIdx] # copy first stmtlist
  node.del firstStmtListIdx, node.len-1 # delete all stmtlists

func parsePatterns(node: NimNode, pats: var InputNodes, insideBracket, insideIncl: bool) =
  matchAst(node, matchErrors):
  of `call` @ nnkCall:
    if insideIncl:
      pats.inclCalls.add call
    else:
      pats.exclCalls.add call
  of nnkPrefix(ident"^", `pat` @ _):
    if insideIncl:
      parsePatterns(pat, pats, insideBracket, false)
    else: error("double negation not supported")
  of nnkStrLit:
    if insideIncl:
      pats.pats.addLit node
    else:
      pats.pats.addLit node, true
  of nnkRStrLit:
    if insideIncl:
      pats.pats.addLit node
    else:
      pats.pats.addLit node, true
  of `patterns` @ nnkBracket:
    if not insideIncl:
      error "excluding a list is not impl'd"
    if not insideBracket:
      for pattern in patterns:
        parsePatterns(pattern, pats, true, true)
    else:
      error "only one level of brackets"
  of nnkCurly(nnkCurly(`varIdent` @ nnkIdent)):
    if insideIncl:
      pats.inclBins.add varIdent
    else:
      pats.inclBins.add varIdent
  of nnkCallStrLit(ident"glob", `pattern` @ nnkRStrLit):
    if insideIncl:
      pats.pats.addGlob pattern
    else:
      pats.pats.addGlob pattern, true
  of nnkCallStrLit(ident"re", `pattern` @ nnkRStrLit):
    if insideIncl:
      pats.pats.addRe pattern
    else:
      pats.pats.addRe pattern, true
  of nnkCallStrLit(ident"peg", `pattern` @ nnkRStrLit):
    if insideIncl:
      pats.pats.addPeg pattern
    else:
      pats.pats.addPeg pattern, true
  of nnkCallStrLit:
    if insideIncl:
      pats.inclCalls.add node
    else:
      pats.exclCalls.add node
  else:
    debugEcho treeRepr node
    debugEcho matchErrors
    error("here")

func parseOutputs(node: NimNode):
    tuple[outputs: NimNode, otherOutputs: InputNodes] =
  result.otherOutputs = newInputNodes()
  matchAst(node):
  of nnkIdent:
    result.outputs = node
  of nnkInfix(ident"|", `lhs` @ _, `rhs` @ _):
    result.outputs = lhs
    parsePatterns(rhs, result.otherOutputs, false, true)

func parseInputs(node: NimNode):
    tuple[isForEach: bool,
          explicit: InputNodes,
          implicit: InputNodes,
          orderOnly: InputNodes] =
  result.explicit = newInputNodes()
  result.implicit = newInputNodes()
  result.orderOnly = newInputNodes()
  matchAst(node, matchErrors):
  of nnkInfix(ident"||", `lhs` @ _, `orderOnly` @ _):
    matchAst(lhs):
    of nnkInfix(ident"|", `lhs` @ _, `rhs` @ _):
      parsePatterns(lhs, result.explicit, false, true)
      parsePatterns(rhs, result.implicit, false, true)
      parsePatterns(orderOnly, result.orderOnly, false, true)
    else:
      parsePatterns(lhs, result.explicit, false, true)
      parsePatterns(orderOnly, result.orderOnly, false, true)
  of nnkInfix(ident"|", `lhs` @ _, `rhs` @ _):
    parsePatterns(lhs, result.explicit, false, true)
    parsePatterns(rhs, result.implicit, false, true)
  of `explicitInputs` @ nnkCommand:
    if explicitInputs.len == 1:
      result.explicit.inclCalls.add explicitInputs
    else:
      if explicitInputs[0] == ident"foreach":
        result.isForEach = true
        matchAst(explicitInputs[1], matchErrors):
        of nnkInfix(ident"||", `lhs` @ _, `orderOnly` @ _):
          matchAst(lhs):
          of nnkInfix(ident"|", `lhs` @ _, `rhs` @ _):
            parsePatterns(lhs, result.explicit, false, true)
            parsePatterns(rhs, result.implicit, false, true)
            parsePatterns(orderOnly, result.orderOnly, false, true)
          else:
            parsePatterns(lhs, result.explicit, false, true)
            parsePatterns(orderOnly, result.orderOnly, false, true)
        of nnkInfix(ident"|", `lhs` @ _, `rhs` @ _):
          parsePatterns(lhs, result.explicit, false, true)
          parsePatterns(rhs, result.implicit, false, true)
        else:
          parsePatterns(explicitInputs[1], result.explicit, false, true)
      else:
        error "needs impl"
  else:
    parsePatterns(node, result.explicit, false, true)


template makePreamble =
  mixin re
  mixin peg
  template thisFile: string =
    relativePath(instantiationInfo().filename, getCurrentDir())

  template shell(arg: string) =
    doAssert waitForExit(procs.shell arg) == 0

  proc matcheslit(pats: Patterns, input: string): bool =
    for lit in pats.lits:
      if lit == input:
        return true

  proc matchesExpr(pats: Patterns, input: string): bool =
    for glob in pats.globs:
      if globMatch(input, glob):
        return true
    for pat in pats.res:
      if match(input, re(pat)):
        return true
    for pat in pats.pegs:
      if match(input, peg(pat)):
        return true

  iterator foreachLit(explicit: PathPatterns): string =
    for path in explicit.incls.lits:
      if path.fileExists and (path notin explicit.excls.lits):
        yield path
      else:
        diag "doesn't exist: " & path
        yield path

  proc matches(pats: PathPatterns, input: string): bool =
    not pats.excls.matchesExpr(input) and pats.incls.matchesExpr(input)

  iterator paths(explicit: PathPatterns): string =
    for filePath in walkDirRec(".", {pcFile, pcLinkToFile}, {pcDir, pcLinkToDir}, true):
      if explicit.incls.matchesExpr filePath:
        if not explicit.excls.matchesExpr filePath:
          yield filePath

  func toPosixShellCommand(nodes: NimNode): string =
    debugEcho treeRepr nodes

  template buildForEach(outputs, explicit, implicit, orderOnly, env, cmds: untyped; debug = false) =
    # bind toSeq
    for path {.inject.} in paths(explicit):
      # if implicit.matches path:
      #   quit "An explicit input can't also be an implicit input: " & path, QuitFailure
      # if orderOnly.matches path:
      #   quit "An explicit input can't also be an order-only input: " & path, QuitFailure
      template pathParts: auto {.inject.} = path.splitFile
      template pathNoExt: string {.inject.} = pathParts.dir / pathParts.name
      template name: string {.inject.} = pathParts.name
      template ext: string {.inject.} = pathParts.ext
      if not debug:
        cmds
      # else:
      #   debugEcho "explicitInputs = " & path
      #   debugEcho "implicitInputs =" & toSeq(foreachLit(implicit)) --> reduce(it.accu & " " & it.elem)
      #   debugEcho "orderOnlyInputs =" & toSeq(foreachLit(orderOnly)) --> reduce(it.accu & " " & it.elem)
      #   debugEcho outputs & ": $(explicitInputs) $(implicitInputs) $(orderOnlyInputs)"
      #   debugEcho "\t@" & cmds.toPosixShellCommand

  template buildForAll(outputs, explicit, implicit, orderOnly, env, cmds: untyped; debug = false) =
    var paths {.inject.}: seq[string]
    for path in foreach(explicit):
      if implicit.matches path:
        quit "An explicit input can't also be an implicit input: " & path, QuitFailure
      if orderOnly.matches path:
        quit "An explicit input can't also be an order-only input: " & path, QuitFailure
      paths.add path
    template pathsParts: auto {.inject.} = paths --> map(it.splitFile)
    template pathsNoExt: auto {.inject.} = pathsParts --> map(it.dir / it.name)
    template names: auto {.inject.} = pathsParts --> map(it.name)
    template exts: auto {.inject.} = pathsParts --> map(it.ext)
    if not debug:
      cmds
    else:
      debugEcho outputs --> reduce(it.accu & " " & it.elem) & ": $(explicitInputs) $(implicitInputs) $(orderOnlyInputs)"


macro make*(debug = false, rules: untyped) =
  result = newStmtList()
  mixin buildForEach
  matchAst(rules, matchErrors):
  # of nnkInfix(ident"<="):
  of `ruleList` @ nnkStmtList:
    for child in ruleList.children:
      child.matchAst matchErrors:

      of `call` @ nnkCall:
        let cmds = extractCmds(call)
        result.add quote do:
          echo repr `call`

      of nnkInfix(ident"<=", `outputStmt` @ _, `inputStmt` @ _, `cmdStmts` @ nnkStmtList):
        var cmds = extractCmds(cmdStmts)
        if cmds.kind in nnkStringLiterals:
          cmds = newCall(ident"shell", copy cmds)
        debugEcho treeRepr cmds
        let (outputs, otherOutputs) = parseOutputs outputStmt
        let (isForEach, explicit, implicit, orderOnly) = parseInputs inputStmt
        let explicitIdent = ident"explicit"
        let implicitIdent = ident"implicit"
        let orderOnlyIdent = ident"orderOnly"
        template genInit(id, v) =
          result.add newVarStmt(`id`, `v`.pats)
          let litIncls = newDotExpr(newDotExpr(`id`, ident"incls"), ident"lits")
          let litExcls = newDotExpr(newDotExpr(`id`, ident"excls"), ident"lits")
          for call in `v`.inclCalls:
            result.add newCall(ident"add", litIncls, call)
          for bin in `v`.inclBins:
            result.add newCall(ident"add", litIncls, bin)
          for call in `v`.exclCalls:
            result.add newCall(ident"add", litExcls, call)
          for bin in `v`.exclBins:
            result.add newCall(ident"add", litExcls, bin)
        result.add getAst makePreamble()
        genInit explicitIdent, explicit
        genInit implicitIdent, implicit
        genInit orderOnlyIdent, orderOnly
        if isForEach:
          result.add quote do:
            buildForEach `outputs`, `explicitIdent`, `implicitIdent`, `orderOnlyIdent`, nil, `cmds`, `debug`
        else:
          result.add quote do:
            buildForAll `outputs`, `explicitIdent`, `implicitIdent`, `orderOnlyIdent`, nil, `cmds`, `debug`
  # echo repr result


when defined makeDumpTrees:
  static: echo "\nshell cmds"
  dumpTree:
    shell "nim c --out:{{out}} {{in}}"

  static: echo "vars"
  dumpTree:
    {{pathNoExt}}

  static: echo "\nglobs"
  dumpTree:
    "ni?"
    "*.ni{m,ms}"

  static: echo "\nlists"
  dumpTree:
    ["", nnn]

  static: echo "\nfull statements"
  dumpTree:
    # "f" <= "d":
    #   echo %o
    #   echo deps

    # ["f"] <= ["d"]:
    #   echo %o
    #   echo deps

    # (["f", "sdf", "sdsd"] | "orderonly") <= ("d" ^["dd", "t.*"] | "other"):
    #   !sdfsdf
    #   echo %o
    #   echo deps

    pathNoExt <= foreach glob"*.ni{m,ms}" | "otherfile":
      "nim c --out:" & pathNoExt & " " & path

    pathNoExt | {{bin}} <= foreach [^"test.nim", ^glob"*.ni{m,ms}", {{bin}}] | "otherfile" || "orderOnly":
      "nim c --out:" & pathNoExt & " " & path

    pathNoExt | {{bin}} <= foreach [^"test.nim", ^glob"*.ni{m,ms}", {{bin}}] || "orderOnly":
      "nim c --out:" & pathNoExt & " " & path

    pathNoExt <= glob"**/*.nim":
      "nim c --out:" & pathNoExt & " " & path

    pathNoExt <= glob"**/*.nim" || sdasd:
      "nim c --out:" & pathNoExt & " " & path


type
  Le16* = uint16
  Offset* = Le16
  Inode* = Le16
  FileTree* = ref object
    tree*: AVLTree[int, FileNode]
  FileKind* {.size: sizeof(uint16), pure.} = enum
    File = 1
    Dir
    SymLink
    Block
    Char
    Fifo
    Sock
    XFile
    XDir
    XSymLink
    XBlock
    XChar
    XFifo
    XSock
  FileNode* = ref object
    kind*: FileKind
    modTime*: int64
    name*: string
  DirEntry* = ref object
    offset*: Le16
    inodeNumber*: Le16
    kind*: FileKind
    size*: Le16
    name*: string

func newFileTree*: FileTree =
  FileTree(tree: newAVLTree[int, FileNode]())

proc scan*(path: string): FileTree =
  result = newFileTree()
  result.tree.insert 1, FileNode(kind: FileKind.File, modTime: 0.int64, name: "a")

proc `$`*(tree: FileTree): string =
  for (k, v) in inOrderTraversal tree.tree:
    echo v.name
