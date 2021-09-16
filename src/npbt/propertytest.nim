# these modules are used extensively
import std/macros
import std/mersenne
import std/options # need this for counter examples

# these modules have limited use, so be selective
from std/math import floor, log10
from std/strformat import fmt
from std/strutils import join, repeat
from std/sugar import `=>` # XXX: maybe a bust because inference can't keep up
from std/sequtils import toSeq, apply
from std/times import toUnix, getTime

# XXX: Once this is mature enough (repeatability, shrinking, and API) move out
#      of experimental.

## :Author: Saem Ghani
## :License: MIT License
##
## Current Development:
## ====================
## This module implements property based testing facilities. Like most nice
## things there are two major parts of this module:
## 1. core concepts of structured data generation, operations, & property tests
## 2. the API by which the former is expressed
## It's important not to conflate the two, the current way tests are executed
## and reported upon is not relevant to the core as an example of this. Nor is
## the composition of arbitraries, predicates, and random number arbitrarys.
##
## API Evolution:
## --------------
## The API needs evolving, in a few areas:
## 1. definition of arbitrarys
## 2. expression of properties
##
## Arbitrarys: at the very least `chain` or `fmap` is likely required along
## with a number of other combinators that allow for rapid definition of
## arbitrarys. This is likely the most important on the road to being able to
## generate AST allowing for rapidly testing languages features working in
## combinations with each other. This should allow for exacting documentation
## of a spec.
##
## Properties: something that provides some simple combinators that allow for:
## `"some property is true" given arb1 & arb2 & arb3 when somePredicate(a,b,c)`
## Where we have a nice textual description of a spec, declaration of
## assumptions, and the predicate. More complex expressions such as given a
## circumstance (textual + given), many properties predicates can be checked
## including introducing further givens specific to the branch of properties.
## To provide a cleaner API in most circumstances, an API that can take a
## subset of `typedesc`s with associated default arbitraries would remove a lot
## of noise with good defaults.
##
## Core Evolution:
## ---------------
## Evolving the core has a number of areas, the most pressing:
## 1. establishing a strong base of default arbitraries
## 2. shrinking support
## 3. replay failed path in run
##
## Default Arbitraries: a strong base is required to feed NimNode generation so
## valid ASTs can be generated quickly.
##
## Shrinking: automatically generated programs will often contain a lot of
## noise, a shrinking can do much to provide small failure demonstrating
## scenarios.
##
## Replay: when you can generate tests, test suites start taking longer very
## quickly. This is of course a good thing, it's a relfection of the lowered
## cost of rapidly exploring large areas of the input space. Being able to
## re-run only a single failing run that otherwise only shows up towards the
## end of a test battery quickly becomes important.
##
## Heavily inspired by the excellent
## [Fast Check library](https://github.com/dubzzz/fast-check).
##
## Concepts:
## * predicate - a function which given a value indicates true or false
## * arbitrary - arbitrary of arbitrary value for some set of values
## * property - a condition a value must hold to, given a predicate
## * run - test a single value against a property
##
## Future directions:
## * properties with predefined examples -- not purely random
## * before and after run hooks for properties
## * support for multiple random number arbitrarys
## * optimise arbitraries for Map/Filter/etc via variants, but allow extension
## * distribution control
## * model based checking
## * async testing
## * shrinking

import
  ./pbt_types,
  ./pbt_types_execution,
  ./arbitraries_core

export pbt_types, pbt_types_execution, arbitraries_core

#-- API

proc name(ctx: GlobalContext): string =
  if ctx.specNames.len > 0: ctx.specNames[0] else: ""

proc startInnerSpec(ctx: var GlobalContext, name: string) =
  ctx.specNames.add(name)
  ctx.ctxEcho name

proc stopInnerSpec(ctx: var GlobalContext) =
  discard ctx.specNames.pop
  echo "" # empty line to break up the spec

template specAux(globalCtx: var GlobalContext, body: untyped): untyped =
  block:
    template forAll[A](
        name: string = "",
        arb1: Arbitrary[A],
        pred: Predicate[A] # XXX: move the predicate decl inline
        ) {.hint[XDeclaredButNotUsed]: off.} =
      discard execProperty(globalCtx, name, arb1, pred, defAssertPropParams())

    template forAll[A,B](
        name: string = "",
        arb1: Arbitrary[A], arb2: Arbitrary[B],
        pred: Predicate[(A, B)] # XXX: move the predicate decl inline
        ) {.hint[XDeclaredButNotUsed]: off.} =
      discard execProperty(globalCtx, name, arb1, arb2, pred,
                           defAssertPropParams())

    template forAll[A,B,C](
        name: string = "",
        arb1: Arbitrary[A], arb2: Arbitrary[B], arb3: Arbitrary[C],
        pred: Predicate[(A, B, C)] # XXX: move the predicate decl inline
        ) {.hint[XDeclaredButNotUsed]: off.} =
      discard execProperty(globalCtx, name, arb1, arb2, arb3, pred,
                           defAssertPropParams())

    template ctSpec(name: string = "", b: untyped): untyped {.hint[XDeclaredButNotUsed]: off.} =
      {.error: "ctSpec can only be used once at the top level".}

    template spec(name: string = "", b: untyped): untyped =
      globalCtx.startInnerSpec(name)
      block:
        b
      globalCtx.stopInnerSpec()

    if globalCtx.specNames.len > 0:
      echo globalCtx.name, "\n"

    body
    globalCtx

template spec*(n: string = "", body: untyped): untyped =
  var globalCtx = GlobalContext(hasFailure: false,
                                specNames: if n.len > 0: @[n] else: @[])
  discard specAux(globalCtx, body)

  if globalCtx.hasFailure:
    echo "Failed"
    quit(QuitFailure)
  else:
    echo "Success"
    quit(QuitSuccess)

macro ctSpec*(n: string = "", body: untyped): untyped =
  quote do:
    const ctx = block:
      let
        n = `n`
        name = if n.len == 0: "" else: " " & n
      var globalCtx = GlobalContext(hasFailure: false,
                        specNames: if n.len > 0: @[n] else: @[])
      specAux(globalCtx, `body`)
    when ctx.hasFailure:
      {.error: fmt"Compile time spec{name} failed".}

#-- Hackish Tests

  # block:
    # XXX: this tests the failure branch but isn't running right now
    # test failure at the end because the assert exits early
    # let foo = proc(t: ((uint32, uint32))): PTStatus =
    #             let (a, b) = t
    #             case a + b > a
    #             of true: ptPass
    #             of false: ptFail
    # forAll("classic math assumption should fail", uint32Arb(), uint32Arb(), foo)

#-- Macro approach, need to revisit

when false:
  # XXX: need to make these work, they move into the library part
  proc initArbitrary[T: tuple]: Arbitrary[T] =
    # Temporary procedure we need to figure out how to make for *all* types
    let size = 100u32
    result = Arbitrary[T](
      mgenerate: proc(arb: Arbitrary[T], rng: var Random): Shrinkable[T] =
        var a = default T
        for field in a.fields:
          field = type(field)(rng.nextUint32() mod size)
    )

  macro execProperty*(name: string, values: varargs[typed],
                        params = defAssertPropParams(), body: untyped): untyped =
    ## Arberates and runs a property. Currently this auto-generates parameter
    ## names from a to z based on the tuple width -- 26 parameters is good enough
    ## for now.
    # XXX: do we want to make the parameter naming explicit?
    var tupleTyp = nnkTupleConstr.newTree()
    let
      isTuple = values.kind == nnkBracket and values[0].kind == nnkTupleConstr
      values = if isTuple: values[0] else: values
      possibleIdents = {'a'..'z'}.toSeq
      idents = block: # Arberate the tuple, and the name unpack varaibles
        var
          idents: seq[NimNode]
        for i, x in values:
          let retT = x[0].getImpl[3][0][1]
          idents.add ident($possibleIdents[i])
          tupleTyp.add retT
        idents

    # make the `let (a, b ...) = input`
    let unpackNode = nnkLetSection.newTree(nnkVarTuple.newTree(idents))
    unpackNode[0].add newEmptyNode(), ident"input"

    body.insert 0, unpackNode # add unpacking to the first step

    result = newStmtList()
    result.add newProc(ident"test",
                      [
                        ident"PTStatus",
                        newIdentDefs(ident"input", tupleTyp, newEmptyNode())
                      ],
                      body) # Emit the proc
    result.add quote do:
      var
        arb = initArbitrary[`tupleTyp`]()
        report = startReport[`tupleTyp`](`name`)
        rng = `params`.random
        p = newProperty(arb, test)
      while report.runId < `params`.runsBeforeSuccess:
        report.startRun()
        let
          s: Shrinkable[`tupleTyp`] = p.generate(rng, report.runId)
          r: PTStatus = p.run(s.value)
          didSucceed = r notin {ptFail, ptPreCondFail}

        if not didSucceed:
          report.recordFailure(s.value, r)

      # XXX: useful for debugging the macro code
      # echo result.repr

      echo report
      if report.hasFailure:
        doAssert report.isSuccessful, $report
