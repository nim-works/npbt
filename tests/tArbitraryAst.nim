import npbt, npbt/arbitraries_ast
import std/macros

const
  nimAstSpec* = astSpec(NimNode, NimNodeKind):
    nnkInfix:
      0 as "op": nnkIdent
      1 .. 2 as "operands": _
      ?3 as "body": nnkStmtList


    nnkTryStmt:
      0 .. ^1 as "exceptions":
        nnkExceptBranch:
          1 .. ^2 as "capture":
            nnkSym
            nnkIdent
            nnkInfix:
              0: nnkIdent(strVal: "as")
              1: nnkIdent
              2: nnkIdent

generateConstructors(nimAstSpec, {nnkEmpty}, newTree)
