## Module implements arbitraries for generating of the syntax trees
## according to the structure specification

import ./ast_spec, ./arbitraries_core, ./pbt_types
export ast_spec

type
  AstBuilder[N, K] = object
    ## Collection of callbacks to construct different classes of the AST
    newTree*: proc(kind: K, subnodes: seq[N]): N ## Tree with subnodes
    newStringLeaf*: proc(kind: K, value: string): N ## String leaf
                                                    ## (literal, ident
                                                    ## etc.)
    newIntLeaf*: proc(kind: K, value: BiggestInt): N ## Integer leaf (literal)
    newFloatLeaf*: proc(kind: K, value: float): N ## Float leaf (literal)
    # TODO embed string builders for arbitrary node values (integer,
    # string, identifiers etc). This would require mapping out different
    # node categories - for exmple string must be split into string
    # literals and identifiers.

  AstNodeClass = enum
    ## Classes of the node kinds
    tncIntLeaf
    tncStringLeaf
    tncFloatLeaf
    tncSubtree

proc newTreeBuilder*[N, K](
    newTree: proc(kind: K, subnodes: seq[N]): N,
    newStringLeaf: proc(kind: K, value: string): N = nil,
    newIntLeaf: proc(kind: K, value: BiggestInt): N = nil,
    newFloatLeaf: proc(kind: K, value: float): N = nil
  ): AstBuilder[N, K] =
  ## Construct new ast tree builder using provided callbacks. Note that all
  ## of the leaf ones are defaulted to `nil`, so if you plan for your tree
  ## to include int/string/float nodes those must also be specified.

  AstBuilder[N, K](
    newTree: newTree,
    newStringLeaf: newStringLeaf,
    newIntLeaf: newIntLeaf,
    newFloatLeaf: newFloatLeaf
  )

proc newTree*[N, K](
  builder: AstBuilder[N, K], kind: K, subnodes: varargs[N]): N =
  ## Construct new tree with subnodes using builder implementation callback
  builder.newTree(kind, @subnodes)

proc newLit*[N, K](builder: AstBuilder[N, K], kind: K, value: string): N =
  ## Construct new string literal using builder implementation callback
  builder.newStringLeaf(kind, value)

proc newLit*[N, K](
    builder: AstBuilder[N, K], kind: K, value: SomeInteger): N =
  ## Construct new integer literal using builder implementation callback
  builder.newStringLeaf(kind, BiggestInt(value))

proc newLit*[N, K](builder: AstBuilder[N, K], kind: K, value: float): N =
  ## Construct new float literal using builder implementation callback
  builder.newFloatLeaf(kind, value)

proc arbAst*[N, K](
    spec: AstSpec[N, K],
    builder: AstBuilder[N, K],
    maxdepth: int = 2,
    maxcount: int = 20,
    maxExtraSubnodes: int = 3
  ): Arbitrary[N] =

  ## - @arg{maxExtraSubnodes} :: Number of *extra* nodes that would be added
  ##   for node kinds with non-concrete ranges. For exampler, if `nnkIfStmt`
  ##   is generated it might have from one to three subnodes (with default
  ##   arguments). But `nnkElifBranch` does not have variable number of
  ##   allowed nodes, so it would only generate one node.
  ## - @arg{maxcount} :: Total number of nodes in generated tree
  ## - @arg{maxdepth} :: Max depth of the generated tree

  let arbKind: Arbitrary[K] = arbEnum(spec.getFilled())

  var size: int = 0
  proc aux(pattern: AstPattern[N, K], depth: int): N =
    if depth < maxdepth:
      var subnodes: seq[N]
      return builder.newTree(pattern.thisKind, subnodes)

    else:
      assert false



  proc generate(arg: Arbitrary[N], rng: var Random): Shrinkable[N] =
    return spec.getPattern(arbKind.generate(rng).value).aux(0).shrinkableOf()

  return arbitrary[N](generate)
