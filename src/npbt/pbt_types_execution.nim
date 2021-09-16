import std/[options]

from std/strformat import fmt
from std/times import toUnix, getTime
from std/strutils import repeat

import ./pbt_types

type
  RunExecution*[T] = object
    ## result of run execution
    # XXX: move to using this rather than open state in `execProperty` procs
    # XXX: lots to do to finish this:
    #      * save necessary state for quick reproduction (path, etc)
    #      * support async and streaming (iterator? CPS? magical other thing?)
    runId*: uint32
    failureOn*: PossibleRunId
    seed*: uint32
    counterExample*: Option[T]

  GlobalContext* = object
    hasFailure*: bool
    specNames*: seq[string]
    # compileTime: bool      ## are we executing the property at compile time
    # ctOutput: string       ## the output generated

  AssertReport*[T] = object
    ## result of a property assertion, with all runs information
    # XXX: don't need counter example and generic param here once
    #      `RunExecution` is being used.
    name*: string
    runId*: PossibleRunId
    failures*: uint32
    firstFailure*: PossibleRunId
    failureType*: PTStatus
    seed*: uint32
    counterExample*: Option[T]

  AssertParams* = object
    ## parameters for asserting properties
    # XXX: add more params to control tests, eg:
    #      * `examples` as a seq[T], for default values
    seed*: uint32
    random*: Random
    runsBeforeSuccess*: range[1..high(int)]
    shrinkFirstFails*: range[1..high(int)]


proc startRun*[T](r: var AssertReport[T]) {.inline.} =
  r.runId.startRun()

proc recordFailure*[T](r: var AssertReport[T], example: T,
                      ft: PTStatus) =
  ## records the failure in the report, and notes first failure and associated
  ## counter-example as necessary
  assert ft in {ptFail, ptPreCondFail}, fmt"invalid failure status: {ft}"
  if r.firstFailure.isUnspecified():
    r.firstFailure = r.runId
    r.counterExample = some(example)
  inc r.failures
  when defined(debug):
    let exampleStr = $example.get() # XXX: handle non-stringable stuff
    echo fmt"Fail({r.runId}): {ft} - {exampleStr}"

proc hasFailure*(r: AssertReport): bool =
  result = not r.firstFailure.isUnspecified()

proc isSuccessful*(r: AssertReport): bool =
  result = r.firstFailure.isUnspecified()

proc `$`*[T](r: AssertReport[T]): string =
  # XXX: make this less ugly
  let status =
    if r.hasFailure:
      fmt"failures: {r.failures}, firstFailure: {r.firstFailure}, firstFailureType: {r.failureType}, counter-example: {r.counterExample}, seed: {r.seed}"
    else:
      "status: success"

  result = fmt"{r.name} - {status}, totalRuns: {r.runId.int}"

proc startReport*[T](
    name: string,
    seed: uint32
  ): AssertReport[T] =
  ## start a new report
  result = AssertReport[T](
    name: name, runId: noRunId,
    failures: 0, seed: seed,
    firstFailure: noRunId, counterExample: none[T]())

proc timeToUint32(): uint32 {.inline.} =
  when nimvm:
    # XXX: can't access time in the VM, figure out another way
    0
  else:
    cast[uint32](clamp(toUnix(getTime()), 0'i64, uint32.high.int64))


proc defAssertPropParams(): AssertParams =
  ## default params used for an `execProperty`
  let seed: uint32 = timeToUint32()
  result = AssertParams(
    seed: seed,
    random: newRandom(seed),
    runsBeforeSuccess: 10,
    shrinkFirstFails: 2
  )

proc indent(ctx: GlobalContext): string =
  '\t'.repeat(max(ctx.specNames.len - 2, 0))

proc ctxEcho*(ctx: GlobalContext, msg: string) =
  discard
  # echo ctx.indent, msg

proc reportSuccess*(ctx: GlobalContext, msg: string) =
  ## XXX: do better reporting
  ctx.ctxEcho "- " & msg

proc reportFailure*(ctx: var GlobalContext, msg: string) =
  ## XXX: do better reporting
  ctx.hasFailure = true
  ctx.ctxEcho "- " & msg

proc execAndShrink*[T](
    ctx: var GlobalContext,
    value: Shrinkable[T],
    prop: Property[T],
    params: AssertParams = defAssertPropParams()
  ): seq[AssertReport[T]] =

  for value in prop.shrink(value):
    var rep = startReport[T](ctx.specNames[^1], params.seed)
    rep.startRun()
    let res = prop.run(value.value)
    if res in {ptFail, ptPreCondFail}:
      rep.recordFailure(value.value, res)
      result.add rep

proc execProperty*[A](
  ctx: var GlobalContext,
  name: string,
  arb: Arbitrary[A],
  pred: Predicate[A],
  params: AssertParams = defAssertPropParams()): seq[AssertReport[A]] =

  var rep = startReport[A](name, params.seed)
  var
    rng = params.random # XXX: need a var version
    p = newProperty(arb, pred)
    shrinkCount = 0

  while(rep.runId < params.runsBeforeSuccess):
    rep.startRun()
    let
      s: Shrinkable[A] = p.generate(rng, rep.runId)
      r = p.run(s.value)
      didSucceed = r notin {ptFail, ptPreCondFail}

    if not didSucceed:
      rep.recordFailure(s.value, r)
      if shrinkCount < params.shrinkFirstFails:
        result.add execAndShrink(ctx, s, p, params)
        inc shrinkCount

  if rep.hasFailure:
    ctx.reportFailure($rep)

  else:
    ctx.reportSuccess($rep)


proc execProperty*[A, B](
  ctx: var GlobalContext,
  name: string,
  arb1: Arbitrary[A], arb2: Arbitrary[B],
  pred: Predicate[(A, B)],
  params: AssertParams = defAssertPropParams()): AssertReport[(A,B)] =

  result = startReport[(A, B)](name, params.seed)
  var
    rng = params.random # XXX: need a var version
    arb = tupleArb[A,B](arb1, arb2)
    p = newProperty(arb, pred)

  while(result.runId < params.runsBeforeSuccess):
    result.startRun()
    let
      s: Shrinkable[(A,B)] = p.generate(rng, result.runId)
      r = p.run(s.value)
      didSucceed = r notin {ptFail, ptPreCondFail}

    if not didSucceed:
      result.recordFailure(s.value, r)

  if result.hasFailure:
    ctx.reportFailure($result)
  else:
    ctx.reportSuccess($result)

proc execProperty*[A, B, C](
  ctx: var GlobalContext,
  name: string,
  arb1: Arbitrary[A], arb2: Arbitrary[B], arb3: Arbitrary[C],
  pred: Predicate[(A, B, C)],
  params: AssertParams = defAssertPropParams()): AssertReport[(A,B,C)] =

  result = startReport[(A, B, C)](name, params.seed)
  var
    rng = params.random # XXX: need a var version
    arb = tupleArb[A,B,C](arb1, arb2, arb3)
    p = newProperty(arb, pred)

  while(result.runId < params.runsBeforeSuccess):
    result.startRun()
    let
      s: Shrinkable[(A,B,C)] = p.generate(rng, result.runId)
      r = p.run(s.value)
      didSucceed = r notin {ptFail, ptPreCondFail}

    if not didSucceed:
      result.recordFailure(s.value, r)

  if result.hasFailure:
    ctx.reportFailure($result)
  else:
    ctx.reportSuccess($result)
