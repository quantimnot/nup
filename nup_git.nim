## ===============
## Git Integration
## ===============
## 
## TODO
## 
## - [ ] Allow specifying specific blobs to fetch.

import
  std/[macros, strformat, strutils, with],
  pkg/[nup_ext, ast_pattern_matching, gitutils, gitcache]

type
  Iri* = distinct string
  GitRev = distinct string
  FilePath = distinct string
  DirPath = distinct string
  GitMakeExtFlag* {.pure.} = enum
    Mirror
    Worktree
    SharedBareCache
    SparseCheckout
    NoBlobs
    NoTrees
    NoTags
    Shallow
    Mgit
    Bare
  GitMakeExtConf* = object
    flags*: set[GitMakeExtFlag]
    url*: Iri
    rev*: GitRev
    gitDir*: DirPath
    workTree*: DirPath
    filter*: PathPatterns

template impl(n) =
  converter `to n`*(val: string): n = n val
  converter `$`*(val: n): string = string val
impl Iri
impl GitRev
impl DirPath

const defaultConf =
  GitMakeExtConf(
    flags: {SharedBareCache, SparseCheckout, NoBlobs, Worktree, Shallow},
    rev: "HEAD"
  )

makeExt defaultConf, "git":
  # init:
  #   # compile time
  #   GitMakeExtConf(
  #     sparse: true
  #   )

  # printConfig:
  #   echo $defaultConf

  compile:
    template inject(id, val) =
      let `id` {.inject.} = val

    var url, commit: string

    # Parse and rewrite the input statements:
    matchAst(explicitInputs):
    of nnkStrLit:
      url = explicitInputs[0].strVal
      extra.add newAssignment(newDotExpr(ident"extConf", ident"url"), explicitInputs[0])
      extra.add newAssignment(newDotExpr(ident"extConf", ident"rev"), newStrLitNode"HEAD")
    of nnkTupleConstr(`gitUrl` @ nnkStrLit, `gitCommit` @ nnkStrLit):
      extra.add newAssignment(newDotExpr(ident"extConf", ident"url"), gitUrl)
      extra.add newAssignment(newDotExpr(ident"extConf", ident"rev"), gitCommit)
    of nnkTupleConstr(`gitUrl` @ nnkStrLit, `gitCommit` @ nnkStrLit, `filter` @ nnkBracket):
      extra.add newAssignment(newDotExpr(ident"extConf", ident"url"), gitUrl)
      extra.add newAssignment(newDotExpr(ident"extConf", ident"rev"), gitCommit)
      template genInit(id, v) =
        let litIncls = newDotExpr(newDotExpr(`id`, ident"incls"), ident"lits")
        let litExcls = newDotExpr(newDotExpr(`id`, ident"excls"), ident"lits")
        for call in `v`.inclCalls:
          extra.add newCall(ident"add", litIncls, call)
        for bin in `v`.inclBins:
          extra.add newCall(ident"add", litIncls, bin)
        for call in `v`.exclCalls:
          extra.add newCall(ident"add", litExcls, call)
        for bin in `v`.exclBins:
          extra.add newCall(ident"add", litExcls, bin)
      genInit newDotExpr(ident"extConf", ident"filter"), parsePatterns filter

    explicitInputs = newNimNode nnkNilLit

    # Rewrite the output statements:
    if outputs.kind in nnkStringLiterals:
      extra.add newAssignment(newDotExpr(ident"extConf", ident"workTree"), outputs)
    else:
      error "nup git extention expects a single string literal for the output"

    # if SharedBareCache in extConf.flags:
    #   extra.add getAst inject(ident"gitDir", newCall(bindSym"gitCacheDir", newStrLitNode url))
    # else:
    #   extra.add getAst inject(ident"gitDir", outputs.strVal)

  scan:
    if existsEnv"GIT_DIR":
      diag "GIT_DIR is set, but it is not yet supported"

    if dirExists extConf.workTree:
      diag &"workdir exists"
      if gitIsWorktree extConf.workTree:
        let workTreeGitDir = gitGitDir extConf.workTree
        diag "workdir is worktree pointing to " & workTreeGitDir

    if dirExists extConf.gitDir:
      diag &"git dir exists: {extConf.gitDir}"

    if NoNetwork in flags:
      diag "NoNetwork option is set; not doing anything!"

    if SharedBareCache in extConf.flags:
      diag "using shared bare git dir"

    if gitRevExists(extConf.gitDir, extConf.rev):
      diag extConf.rev & " exists"
    else:
      diag extConf.rev & " does *NOT* exist"
      # TODO: add option to fetch

    if not gitSymRefAlwaysResolvesToSameObject(extConf.gitDir, extConf.rev):
      diag extConf.rev & " doesn't refer to a specific commit"

    # TODO: save scan results

  update:
    var gitCloneFlags {.inject.}: string
    var gitDir {.inject.} = outputs
    for flag in extConf.flags:
      case flag
      of Mirror:
        gitCloneFlags &= " --mirror"
      of Shallow:
        if gitCommit == "HEAD":
          gitCloneFlags &= " --depth=1"
      of NoBlobs:
        gitCloneFlags &= " --filter=blob:none"
      of NoTrees:
        gitCloneFlags &= " --filter=tree:0"
      of SparseCheckout:
        gitCloneFlags &= " --no-checkout"
      of SharedBareCache:
        gitCloneFlags &= " --bare"
        gitDir = gitCacheDir gitUrl
      of Worktree:
        gitCloneFlags &= " --no-checkout"
      else: diag "unhandled flag: " & flag

    discard gitOrQuit &"clone {gitCloneFlags} {gitUrl} {gitDir}"

    let makeRuleId = "FIXMEEEEE" # TODO: create a rule id for each rule

    if ({Mirror, SparseCheckout, Worktree, SharedBareCache} * extConf.flags).card > 0:
      discard gitOrQuit &"--git-dir={gitDir} worktree add --no-checkout {outputs} {gitCommit}"

      # https://morgan.cugerone.com/blog/workarounds-to-git-worktree-using-bare-repository-and-cannot-fetch-remote-branches/
      discard gitOrQuit &"--git-dir={gitDir} remote.origin.fetch '+refs/heads/*:refs/remotes/origin/*'"

      withDir outputs:
        let gitFilteredPathsFilename = getTempDir() / makeRuleId & "_gitFilteredPaths"
        block:
          var gitFilteredPathsFile = open(gitFilteredPathsFilename, fmWrite)
          for path in gitOrQuit"ls-tree -r --name-only HEAD".splitLines:
            if gitFilterPats.matches path:
              gitFilteredPathsFile.writeLine path
          close gitFilteredPathsFile
        discard gitOrQuit "restore --staged --pathspec-from-file " & gitFilteredPathsFilename
        discard gitOrQuit "restore --pathspec-from-file " & gitFilteredPathsFilename
        removeFile gitFilteredPathsFilename


makeConf "git", GitMakeExtConf:
  extConf.flags.incl Mgit
