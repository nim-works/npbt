import
  std/[options, macros, sequtils, strutils, parseutils, tables]

## This module implements a schema-like description of the AST.

func concat(args: varargs[string, `$`]): string = args.join("")
func newEqE(lhs, rhs: NimNode): NimNode = nnkExprEqExpr.newTree(lhs, rhs)
func newEcE(lhs, rhs: NimNode): NimNode = nnkExprColonExpr.newTree(lhs, rhs)
func newEqE(lhs: string, rhs: NimNode): NimNode = newEqE(ident(lhs), rhs)
func newEcE(lhs: string, rhs: NimNode): NimNode = newEcE(ident(lhs), rhs)

type
  AstRangeKind = enum
    akPoint ## `idx`
    akInversePoint ## `^idx`
    akDirectSlice ## `idx1 .. idx2`
    akInverseSlice ## `^idx1 .. ^idx2`
    akMixedSlice ## `idx1 .. ^idx2`


  AstRange = object
    optional*: bool
    doc*: string
    name*: string
    case kind*: AstRangeKind
      of akPoint, akInversePoint:
        idx*: int

      of akDirectSlice, akInverseSlice, akMixedSlice:
        start*: int
        finish*: int

  AstCheckFail[K] = object
    isMissing*: bool ## Expected node in the range but got nothing?
    msg*: string ## Message describing failure
    path*: seq[int] ## Full path to current node from the root of the tree
    parent*: K ## Type of the parent node
    expected*: set[K] ## Set of possible node kinds expected in the AST range
    arange*: AstRange ## Examined AST range
    nested*: seq[AstCheckFail[K]] ## Failures for subnode validation

  AstCheckError = object of CatchableError

  AstCheckProc*[N, K] = proc(node: N): Option[AstCheckFail[K]]

  AstPatternRange[N, K] = tuple[arange: AstRange, alts: seq[AstPattern[N, K]]]

  AstPattern*[N, K] = object
    thisKind*: K
    doc*: string
    check*: AstCheckProc[N, K]
    expected*: set[K]
    ranges*: seq[AstPatternRange[N, K]]

  AstSpec*[N, K] = object
    filled: set[K]
    spec: array[K, Option[AstPattern[N, K]]]

func astPattern*[N, K](
    expected: set[K],
    this: K,
    check: AstCheckProc[N, K] = nil,
    doc: string = ""
  ): AstPattern[N, K] =

  AstPattern[N, K](expected: expected, check: check, thisKind: this)


func astPattern*[N, K](
    expected: set[K],
    this: K,
    alts: openarray[AstPatternRange[N, K]],
    check: AstCheckProc[N, K] = nil,
    doc: string = ""
  ): AstPattern[N, K] =

  AstPattern[N, K](
    expected: expected, ranges: @alts, check: check,
    doc: doc, thisKind: this)

func astPattern*[N, K](
    alts: openarray[AstPatternRange[N, K]],
    this: K,
    check: AstCheckProc[N, K] = nil,
    doc: string = ""
  ): AstPattern[N, K] =

  AstPattern[N, K](ranges: @alts, check: check, doc: doc, thisKind: this)

func astPattern*[N, K](doc: string = ""): AstPattern[N, K] =
  AstPattern[N, K](doc: doc)

func astSpec*[N, K](
    patterns: openarray[(K, AstPattern[N, K])]): AstSpec[N, K] =
  for (kind, pattern) in patterns:
    result.spec[kind] = some pattern
    result.filled.incl kind

func getPattern*[N, K](spec: AstSpec[N, K], kind: K): AstPattern[N, K] =
  spec.spec[kind].get()

func getFilled*[N, K](spec: AstSpec[N, K]): set[K] = spec.filled

func getNodeRanges*[N, K](spec: AstSpec[N, K]): array[K, Table[string, AstRange]] =
  for kind, pattern in spec.spec:
    if pattern.isSome():
      for arange in pattern.get().ranges:
        if arange.arange.name.len > 0:
          result[kind][arange.arange.name] = arange.arange

template noPositional(spec, node, name): untyped {.dirty.} =
  var names: string
  if table[node.kind].len > 0:
    names = "Available names - "
    for name, _ in pairs(table[node.kind]):
      names.add ", "
      names.add name

  else:
    names = "No named subnodes specified."


  raise newException(
    KeyError,
    concat(
      "Cannot get positional node with name '", name,
      "' from node of kind '", $node.kind, "'. ", names))


func getSingleSubnodeIdx*[N, K](
    spec: static[AstSpec[N, K]], node: N, name: string): int =
  const table = getNodeRanges(spec)
  if name in table[node.kind]:
    let arange = table[node.kind][name]
    let slice = arange.toSlice(len(node))
    assert slice.a < len(node), concat(
      "Range ", name, " for node kind ", $node.kind,
      " was resolved into slice ", $slice, "(required ast range is ",
      $arange, ")")

    return slice.a

  else:
    noPositional(spec, node, name)

func getSingleSubnode*[N, K](
    spec: static[AstSpec[N, K]], node: N, name: string): N =
  node[getSingleSubnodeIDx(spec, node, name)]

func getMultipleSubnode*[N, K](
    spec: static[AstSpec[N, K]], node: N, name: string): seq[N] =
  const table = getNodeRanges(spec)
  if name in table[node.kind]:
    let arange = table[node.kind][name]
    let slice = arange.toSlice(len(node))
    for idx in slice:
      assert idx < len(node), concat(
        "Range ", name, " for node kind ", $node.kind,
        " was resolved into slice ", $slice, "(required ast range is ",
        $arange, ")"
      )

      result.add node[idx]

  else:
    noPositional(spec, node, name)

func fieldRange*[N, K](
    spec: AstSpec[N, K], node: N, idx: int): Option[AstRange] =
  if spec.spec[node.kind].isSome():
    let pattern = spec.spec[node.kind].get()
    for field in pattern.ranges:
      if field.arange.contains(idx, node.len):
        return some field.arange


func fieldName*[N, K](
    spec: AstSpec[N, K], node: N, idx: int): Option[string] =

  let field = spec.fieldRange(node, idx)
  if field.isSome():
    return some field.get().name

func fieldDoc*[N, K](
    spec: AstSpec[N, K], node: N, idx: int): Option[string] =

  let field = spec.fieldRange(node, idx)
  if field.isSome():
    return some field.get().doc


func astRange*(
    idx: int, optional: bool = false,
    doc: string = "", name: string = ""): AstRange =
  AstRange(
    kind: akPoint, idx: idx, optional: optional,
    doc: doc, name: name)

func astRange*(
    idx: BackwardsIndex,
    optional: bool = false,
    doc: string = "",
    name: string = ""
  ): AstRange =
  AstRange(
    kind: akInversePoint, idx: idx.int, name: name,
    optional: optional, doc: doc)

func astRange*(
    slice: Slice[int],
    optional: bool = false,
    doc: string = "",
    name: string = ""
  ): AstRange =
  AstRange(
    kind: akDirectSlice, start: slice.a, doc: doc, name: name,
    finish: slice.b, optional: optional)

func astRange*(
    slice: HSlice[int, BackwardsIndex],
    optional: bool = false,
    doc: string = "",
    name: string = ""
  ): AstRange =
  AstRange(
    kind: akMixedSlice, start: slice.a, doc: doc, name: name,
    finish: slice.b.int, optional: optional)

func astRange*(
    slice: Slice[BackwardsIndex],
    optional: bool = false,
    doc: string = "",
    name: string = ""
  ): AstRAnge =
  AstRange(
    kind: akInverseSlice, start: slice.a.int, doc: doc, name: name,
    finish: slice.b.int, optional: optional)


macro astSpec*(nodeType, kindType, body: untyped): untyped =
  let
    nodeType = copyNimNode(nodeType)
    kindType = copyNimNode(kindType)

  proc call(name: string): NimNode =
    nnkBracketExpr.newTree(ident(name), nodeType, kindType)


  proc aux(node: NimNode, thisKind: NimNode): NimNode
  proc rangeCurly(node: NimNode, thisKind: NimNode): NimNode

  proc toSet(node: NimNode): NimNode =
    case node.kind:
      of nnkCurly:
        return node

      of nnkIdent:
        return nnkCurly.newTree(node)

      of nnkInfix:
        proc unpack(node: NimNode): seq[NimNode] =
          if node.kind == nnkIdent:
            result.add node

          else:
            if not node[0].eqIdent("or"):
              error("Expected infix `or` for alternative node kind values", node[0])

            result.add unpack(node[1])
            result.add unpack(node[2])

        if node[0].eqIdent("or"):
          return nnkCurly.newTree(unpack(node))

        else:
          return nnkCurly.newTree()

      else:
        expectKind(node, {nnkInfix, nnkCurly, nnkIdent})


  proc altList(node: NimNode, comment: var string, thisKind: NimNode): NimNode =
    result = nnkBracket.newTree()
    var itemCount = 0
    for kind in node:
      case kind.kind:
        of nnkIdent:
          if kind.eqIdent("_"):
            discard

          else:
            inc itemCount
            result.add newCall(call"astPattern", toSet(kind), thisKind)

        of nnkInfix:
          inc itemCount
          result.add newCall(call"astPattern", toSet(kind), thisKind)

        of nnkCall:
          inc itemCount
          result.add newCall(
            call"astPattern", toSet(kind[0]), thisKind, rangeCurly(kind[1], thisKind))

        of nnkObjConstr:
          inc itemCount
          var check = newStmtList()
          let nodeId = ident("node")

          result.add newCall(
            call"astPattern",
            toSet(kind[0]),
            thisKind,
            quote do:
              proc node(`nodeId`: `nodeType`): Option[AstCheckFail[`kindType`]] =
                discard

              node
          )

        of nnkCommentStmt:
          if itemCount == 0:
            comment = kind.strVal()

          else:
            result[^1].add newTree(
              nnkExprEqExpr, ident"doc", newLit(kind.strVal()))

        else:
          expectKind(
            kind, {nnkIdent, nnkCall, nnkObjConstr, nnkCommentStmt})


    if result.len == 0:
      result = newCall(
        nnkBracketExpr.newTree(
          ident"newSeq",
          nnkBracketExpr.newTree(
            ident"AstPattern", nodeType, kindType)))

    else:
      result = nnkPrefix.newTree(ident"@", result)


  proc splitRange(check: NimNode): tuple[arange: NimNode, name: NimNode, isOpt: bool] =
    result.name = newLit("")
    if check.kind == nnkInfix and check[0].eqIdent(".."):
      result.arange = nnkInfix.newTree(check[0 .. 2])

    elif check.kind == nnkInfix and check[0].eqIdent("as"):
      if check[1].kind == nnkPrefix and check[1][0].eqIdent("?"):
        result.arange = check[1][1]
        result.isOpt = true

      else:
        result.arange = check[1]

      result.name = check[2]

    elif check.kind == nnkPrefix:
      if check[0].eqIdent("?"):
        result.arange = check[1]
        result.isOpt = true

      else:
        result.arange = nnkPrefix.newTree(check[0 .. 1])

    elif check.kind == nnkInfix and check[0].eqIdent("..^"):
      result.arange = nnkInfix.newTree(
        ident"..",
        check[1],
        nnkPrefix.newTree(ident"^", check[2]))

    else:
      assert false, "#[ TODO ]#"

  proc rangeCurly(node: NimNode, thisKind: NimNode): NimNode =
    result = nnkTableConstr.newTree()
    for check in node:
      var comment: string = ""
      case check.kind:
        of nnkInfix, nnkPrefix:
          let (arange, name, isOpt) = splitRange(check)

          if (check.kind == nnkInfix and check.len == 4) or
               (check.kind == nnkPrefix and check.len == 3):
            let list = altList(check[^1], comment, thisKind)
            result.add newEcE(
              newCall(
                ident"astRange",
                arange,
                newEqE("optional", newLit(isOpt)),
                newEqE("doc", newLit(comment)),
                newEqE("name", name)),
              list)

          else:
            result.add newEcE(
              newCall(
                ident"astRange",
                arange,
                newEqE("doc", newLit(comment)),
                newEqE("name", name)),
              nnkPrefix.newTree(
                ident"@",
                nnkBracket.newTree(
                  newCall(call"astPattern", thisKind))))

        of nnkCall:
          let list = altList(check[1], comment, thisKind)
          result.add newEcE(
            newCall(ident"astRange", check[0], newEqE("doc", newLit(comment))), list)

        else:
          expectKind(check, {nnkInfix, nnkCall})


  proc aux(node: NimNode, thisKind: NimNode): NimNode =
    case node.kind:
      of nnkStmtList:
        if allIt(
          node, it.kind == nnkIdent or
          (it.kind == nnkCall and it[0].kind == nnkIdent)):
          var comment = ""
          echo node.treeRepr()
          let thisKind = node[0][0]
          let list = altList(node, comment, thisKind)
          result = newCall(call"astPattern", list, thisKind, newEqE("doc", newLit(comment)))

        else:
          result = newCall(call"astPattern", rangeCurly(node, thisKind), thisKind)

      else:
        assert false, $node.kind



  result = nnkTableConstr.newTree()
  for pattern in body:
    expectKind(pattern, {nnkCall})
    result.add newEcE(pattern[0], aux(pattern[1], pattern[0]))

  result = newCall(call"astSpec", result)


func toSlice*(arange: AstRange, maxLen: int): Slice[int] =
  case arange.kind:
    of akPoint: arange.idx .. arange.idx
    of akInversePoint: (maxLen - arange.idx) .. (maxLen - arange.idx)
    of akDirectSlice: arange.start .. arange.finish
    of akInverseSlice: (maxLen - arange.start) .. (maxLen - arange.finish)
    of akMixedSlice: arange.start .. (maxLen - arange.finish)

func contains*(arange: AstRange, idx, maxLen: int): bool =
  idx in toSlice(arange, maxLen)

func `$`*(arange: AstRange): string =
  case arange.kind:
    of akPoint: $arange.idx
    of akInversePoint: "^" & $arange.idx
    of akDirectSlice: $arange.start & ".." & $arange.finish
    of akInverseSlice: "^" & $arange.start & "..^" & $arange.finish
    of akMixedSlice: $arange.start & "..^" & $arange.finish

func `$`*[N, K](spec: AstPattern[N, K]): string =
  result.add $spec.expected

proc toPath*[N](ast: N, path: seq[int]): string =
  when ast is ref:
    if isNil(ast):
      return join(path.mapIt("[" & $it & "]"), ".")

  mixin `[]`
  proc aux(a: N, path: seq[int]): seq[string] =
    result.add $a.kind
    if path.len > 1:
      result.add aux(a[path[0]], path[1..^1])

    elif path.len == 1:
      result.add "[" & $path[0] & "]"

  return join(aux(ast, path), ".")

proc isEmpty*[K](fail: AstCheckFail[K], withNested: bool = true): bool =
  fail.isMissing.not() and
  fail.msg.len == 0 and
  fail.expected.len == 0 and
  (if withNested: fail.nested.len == 0 else: true)

proc findMissing*[N, K](
    spec: AstPattern[N, K], node: N, path: seq[int] = @[]): AstCheckFail[K] =
  result.path = path
  # Validate all subnodes of `node` against specified subranges.
  if spec.ranges.len > 0:
    var altFound = newSeqWith(spec.ranges.len, false)

    var idx = 0
    while idx < node.len:
      # Find matching node range for index
      for rangeIdx, arange in spec.ranges:
        if arange.arange.contains(idx, node.len):
          # Mark as found
          altFound[rangeIdx] = true

          for alt in arange.alts:
            let n = findMissing(alt, node, path & @[idx])
            if not n.isEmpty():
              result.nested.add n

          break

      inc idx

    # Show all missing ranges
    for rangeIdx, found in altFound:
      if (not found) and (not spec.ranges[rangeIdx].arange.optional):
        var expected: set[K]
        for alt in spec.ranges[rangeIdx].alts:
          expected.incl alt.expected

        result.nested.add AstCheckFail[K](
          isMissing: true,
          parent: node.kind,
          path: path & rangeIdx,
          arange: spec.ranges[rangeIdx].arange,
          expected: expected)


proc validateAst*[N, K](
    spec: AstPattern[N, K], kind, subnode: K,
    idx: int, maxLen: int, path: seq[int] = @[]
  ): AstCheckFail[K] =

  result.path = path
  for arange in spec.ranges:
    if arange.arange.contains(idx, maxLen):
      for alt in arange.alts:
        if subnode notin alt.expected:
          result.nested.add AstCheckFail[K](
            parent: kind,
            path: path,
            expected: alt.expected,
            arange: arange.arange)

proc treeRepr*[N, K](spec: AstSpec[N, K]): string =
  proc aux(p: AstPattern[N, K], level: int, r: var string) =
    r.add repeat("  ", level)

    if p.doc.len > 0:
      r.add p.doc.indent(level + 1)

    if p.expected.len > 0:
      r.add p.expected

    for arange in p.ranges:
      r.add "\n"
      r.add "  ".repeat(level + 1)
      r.add $arange.arange
      if arange.arange.name.len > 0:
        r.add " "
        r.add arange.arange.name

      for alt in arange.alts:
        r.add "\n"
        aux(alt, level + 2)

  for kind, pattern in pairs(spec.spec):
    if pattern.isSome():
      result.add kind
      result.add "\n"
      aux(pattern.get(), 1, result)
      result.add "\n"




proc formatFail*[N, K](fail: AstCheckFail[K], node: N): string =
  proc aux(fail: AstCheckFail[K], level: int, r: var string) =
    r.add repeat("  ", level)
    if fail.isEmpty(withNested = false):
      discard

    else:
      if fail.msg.len > 0:
        r.add fail.msg
        r.add " "

      if fail.expected.len > 0:
        if fail.isMissing:
          r.add "missing subnode "
          r.add $fail.arange
          if fail.arange.name.len > 0:
            r.add " ("
            r.add fail.arange.name
            r.add ")"

          r.add " "
          r.add $fail.expected

        else:
          r.add "wanted "
          r.add $fail.expected
          r.add " in "
          r.add $fail.arange
          if fail.arange.name.len > 0:
            r.add " ("
            r.add fail.arange.name
            r.add ")"

      else:
        if fail.isMissing:
          r.add "missing subnode "
          r.add $fail.arange
          if fail.arange.name.len > 0:
            r.add " ("
            r.add fail.arange.name
            r.add ")"

      if fail.path.len > 0:
        r.add " on path "
        r.add toPath(node, fail.path)

      else:
        r.add " for "
        r.add $fail.parent

      if fail.arange.doc.len > 0:
        r.add "\n"
        r.add fail.arange.doc.indent(level * 2 + 2)

    for nested in fail.nested:
      if not nested.isEmpty():
        r.add "\n"
        aux(nested, level + 1, r)

  aux(fail, 0, result)


proc validateAst*[N, K](
    spec: AstSpec[N, K], node: N, subnode: N, idx: int): string =

  if spec.spec[node.kind].isSome():
    result.add formatFail(
      validateAst(
        spec.spec[node.kind].get(),
        node.kind, subnode.kind, idx, node.len, @[idx]), node)

    result.add "\n"
    result.add formatFail(
      findMissing(spec.spec[node.kind].get(), node), node)


proc validateSub*[N, K](
    spec: AstPattern[N, K], node, sub: K, idx, maxIdx: int
  ): Option[string] =

  let fail = formatFail(
    validateAst(spec, node, sub, idx, maxIdx, @[idx]), N(nil))

  if fail.len() > 0:
    return some fail


proc validateSub*[N, K](
    spec: AstSpec[N, K], node: N, idx: int, sub: N): Option[string] =
  if spec.spec[node.kind].isSome():
    let fail = formatFail(
      validateAst(
        spec.spec[node.kind].get(), node.kind, sub.kind, idx, node.len),
      node)

    if fail.len() > 0:
      return some fail


proc validateSub*[N, K](
    spec: AstSpec[N, K], node: N, idx: int): Option[string] =
  validateSub(spec, node, idx, node[idx])

proc validateSelf*[N, K](
    spec: AstSpec[N, K], node: N): Option[string] =
  if spec.spec[node.kind].isSome():
    let fail = formatFail(
      findMissing(spec.spec[node.kind].get(), node), node)

    if fail.len() > 0:
      return some fail

proc validateAst*[N, K](spec: AstSpec[N, K], node: N): string =
  if spec.spec[node.kind].isSome():
    result.add formatFail(
      findMissing(spec.spec[node.kind].get(), node), node)

proc instImpl[N, K](
    spec: AstSpec[N, K],
    defaultable: set[K],
    makeVia: string,
    specId: NimNode,
  ): NimNode =

  let typeName = ident($N)
  let prefixLen = max(0, skipWhile($low(K), {'a' .. 'z'}))

  result = newStmtList()


  proc validate(arg: NimNode, pattern: AstPattern[N, K]): NimNode =
    var cond: NimNode
    var body = newStmtList()

    if pattern.expected.len == 0 and
       pattern.ranges.len == 0:
      cond = newCall("assert", newCall("not", newCall("isNil", arg)))

    else:
      cond = newCall(
        "contains",
        newLit(pattern.expected),
        nnkDotExpr.newTree(arg, ident"kind"))

    return nnkElifBranch.newTree(cond, body)


  for kind, pattern in spec.spec:
    if pattern.isSome():
      var subnodes: seq[NimNode]
      var impl = newStmtList()
      var make = ident("argList")
      var argLen = newCall("len", make)
      var absIdx = 0
      var validation = newStmtList()

      impl.add quote do:
        var `make`: seq[`typeName`]


      for idx, arange in pattern.get().ranges:
        let (arange, alts) = arange
        var name =
          if arange.name.len > 0:
            ident(arange.name)

          else:
            warning("Missing name for subnode #" & $idx & " of " & $kind)
            ident("node" & $idx)

        case arange.kind:
          of akPoint:
            subnodes.add nnkIdentDefs.newTree(name, typeName, newEmptyNode())
            let klit = ident($kind)
            let ilit = newLit(absIdx)
            let lit = newCall("getPattern", specId, kLit)
            let nameLit = newLit(name.strVal())

            validation.add quote do:
              let fail = validateSub(
                `lit`, `klit`, `name`.kind, `ilit`, `argLen`)

              if fail.isSome():
                raise newException(
                  AstCheckError,
                  "Invalid subnode kind for " & `nameLit` & " - " & $fail.get() &
                    ". Current input is " & $`name`.kind)

              `make`.add `name`

            inc absIdx


          of akDirectSlice:
            var subIdx = 0
            for item in arange.start .. arange.finish:
              let name = ident(name.strVal() & "_" & $subIdx)

              subnodes.add nnkIdentDefs.newTree(name, typeName, newEmptyNode())
              inc subIdx

          of akMixedSlice:
            subnodes.add nnkIdentDefs.newTree(
              name,
              nnkBracketExpr.newTree(
                (if idx == pattern.get().ranges.high: ident"varargs" else: ident"seq"),
                typeName),
              newEmptyNode())

            let klit = ident($kind)
            let lit = newCall("getPattern", specId, kLit)
            let nameLit = newLit(name.strVal())
            validation.add quote do:
              for item in items(`name`):
                `make`.add item
                let fail = validateSub(
                  `lit`, `klit`, item.kind, high(`make`), `argLen`)

                if fail.isSome():
                  raise newException(
                    AstCheckError,
                    "Invalid subnode kind for " & `nameLit` & " - " & $fail.get() &
                      ". Current input is " & $item.kind)

          else:
            assert false, $arange & " " & $arange.kind


      impl.add validation

      let idCall = ident($kind)
      let makeCall = ident(makeVia)
      impl.add quote do:
        result = `makeCall`(`idCall`, `make`)

      result.add nnkProcDef.newTree(
        nnkPostfix.newTree(ident"*", ident("new" & ($kind)[prefixLen .. ^1])), # the exported proc name
        newEmptyNode(),
        newEmptyNode(),
        nnkFormalParams.newTree(typeName & subnodes),
        newEmptyNode(),
        newEmptyNode(),
        impl)


template generateConstructors*[N; K: enum](
    inSpec: AstSpec[N, K]{lit | `const`},
    inDefaultable: set[K],
    makeVia: untyped{ident}
  ): untyped =

  bind instImpl
  macro inst(
      spec: static[AstSpec[N, K]],
      defaultable: static[set[K]],
      makeVia: static[string],
      specId: AstSpec[N, K]
    ): untyped =

    instImpl(spec, defaultable, makeVia, specId)

  inst(inSpec, inDefaultable, astToStr(makeVia), inSpec)
