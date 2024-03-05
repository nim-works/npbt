import std/[options]

from std/strformat import fmt
from std/times import toUnix, getTime
from std/strutils import repeat

import ./pbt_types

type
  CounterExample[T] = object
    value*: T ## Value for which property predicate does not return
              ## `ptPas`
    path*: seq[int] ## DOC. Replace with int typedef, this is not
                    ## descriptive enough

  RunExecution*[T] = object
    ## result of run execution
    # XXX: move to using this rather than open state in `execProperty` procs
    # XXX: lots to do to finish this:
    #      * save necessary state for quick reproduction (path, etc)
    #      * support async and streaming (iterator? CPS? magical other thing?)
    runId*: uint32
    failureOn*: PossibleRunId
    seed*: uint32
    name*: string
    counterExample*: Option[CounterExample[T]]

    # REVIEW fields below were added "because fast-check" does this, they
    # might not be actually needed later (see next comments).

    message*: string # QUESTION fast-check stores execution failure
                     # messages in the `RunExecution` objects, but we also
                     # have `AssertReport` object. Should I reuse it
                     # instead? I.e. remove all `failureOn`, `seed` and
                     # other entries, and embed one object in another? This
                     # is probably preferrable, though for now I will
                     # follow fast-check approach.
    numSuccess*: int

  Runner[T] = object
    ## Wrapper around run execution. Holds both value generator and
    ## statistics about run execution.
    # NOTE For now I mirror design of the fast-check, later it might be
    # better to separate properties and source value generator.
    runExecution: RunExecution[T] ## Current state of run execution
    currentIdx: int ## Number of values checked by this runner
    # QUESTION `.runExecution` has `runId` and `failureOn` - they are
    # different from `currentIdx` or not?
    sourceValues: Arbitrary[T] ## Generator of the source values to check

    currentShrinkable: Shrinkable[T] ## Last yielded value. Is stored in
    ## runner instance in order to specify correct value for
    ## `CounterExample`

    mrng: Random ## Current state of the random to pass in the
                 ## `sourceValues` when new value is required.


  RunnerYield[T] = object
    value: Shrinkable[T]
    done: bool

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
    counterExample*: Option[CounterExample[T]]

  AssertParams* = object
    ## parameters for asserting properties
    # XXX: add more params to control tests, eg:
    #      * `examples` as a seq[T], for default values
    seed*: uint32
    random*: Random
    runsBeforeSuccess*: range[1..high(int)]
    shrinkFirstFails*: range[1..high(int)]
    path*: Option[seq[int]]

func hasFailure*[T](ex: RunExecution[T]): bool =
  ex.counterExample.isSome()

proc startRun*[T](r: var AssertReport[T]) {.inline.} =
  r.runId.startRun()

proc recordFailure*[T](r: var AssertReport[T], example: T,
                      ft: PTStatus) =
  ## records the failure in the report, and notes first failure and associated
  ## counter-example as necessary
  assert ft in {ptFail, ptPreCondFail}, fmt"invalid failure status: {ft}"
  if r.firstFailure.isUnspecified():
    r.firstFailure = r.runId
    r.counterExample = some(CounterExample[T](value: example))

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

proc `$`*[T](r: RunExecution[T]): string =
  if r.hasFailure:
    let ce = r.counterExample.get()
    # Use somewhat ugly formatting for path/seed to be able to copy-paste
    # failed things directly, instead of having to reformat them.
    fmt"{r.name} - failed on (path: {ce.path}, seed: {r.seed}) with value {ce.value}"

  else:
    fmt"{r.name} - success on {r.runId.int} runs"

proc startReport*[T](
    name: string,
    seed: uint32
  ): AssertReport[T] =
  ## start a new report
  result = AssertReport[T](
    name: name, runId: noRunId,
    failures: 0, seed: seed,
    firstFailure: noRunId,
    counterExample: none[CounterExample[T]]()
  )

proc defAssertPropParams*(): AssertParams =
  ## default params used for an `execProperty`
  let rand = newRandom()
  result = AssertParams(
    seed: rand.seed,
    random: rand,
    runsBeforeSuccess: 10,
    shrinkFirstFails: 2
  )

proc propParams*(seed: uint32, path: seq[int]): AssertParams =
  ## Construct new assert parameters based on default ones, overriding seed
  ## and path with specified ones.
  result = defAssertPropParams()
  result.seed = seed
  result.random = newRandom(seed)
  result.path = some path

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

proc recordPass*[T](
     execution: var RunExecution[T], value: T) =
  ## Record success of the executiuon
  # QUESTION why is it necessary to store value of the succededing
  # execution? There are (supposedly) hundreds of those, and we are not
  # really interested in them for the most part.
  #
  # NOTE fast-check also builds 'execution tree' where values are used. For
  # now I omitted this part, since I'm not sure what functionality it
  # enables.
  inc execution.numSuccess

proc recordFail*[T](
    execution: var RunExecution[T], value: T, id: int) =
  ## Record failure of the execution, setting counterexample and associated
  ## metadata.
  if execution.counterExample.isNone():
    execution.counterExample = some CounterExample[T](
      value: value,
      path: @[id]
    )

  else:
    assert false # QUESTION I'm still not sure how often `fail` is supposed
                 # to be called exactly. Once per execution run I suppose?
                 # At least this would make sense - once property fails, we
                 # record first failure and move on.


proc newRunner*[T](
    name: string, params: AssertParams, arb: Arbitrary[T]): Runner[T] =
  ## Create new runner object, using specified params.
  result = Runner[T](
    runExecution: RunExecution[T](seed: params.seed, name: name),
    sourceValues: arb,
    mrng: newRandom()
  )

  toss(result.mrng)

proc newRunnerYield*[T](
    shrinkable: Shrinkable[T], done: bool = false): RunnerYield[T] =
  ## Create new runner yield object
  RunnerYield[T](done: done, value: shrinkable)

proc next*[T](runner: var Runner[T]): RunnerYield[T] =
  ## Get next value from arbitrary generator embedded in runner
  runner.currentShrinkable = runner.sourceValues.generate(runner.mrng)
  discard runner.mrng.nextInt()
  inc runner.currentIdx
  return newRunnerYield(runner.currentShrinkable, false)

iterator items*[T](runner: var Runner[T]): RunnerYield[T] =
  ## Iterate over results of the arbitrary generator until no more results
  ## are produced, or until runner detects a run execution failure.
  var res = runner.next()
  while not (res.done or runner.runExecution.hasFailure):
    yield res
    res = runner.next()

proc handleResult*[T](runner: var Runner[T], status: PtStatus) =
  ## This procedure must be called after `next()` (or in every iteration of
  ## the loop over `items`), otherwise recorded failure would not store
  ## correct counterexample value.
  case status:
    of ptPass:
      recordPass(runner.runExecution, runner.currentShrinkable.value)

    of ptFail, ptPreCondFail:
      recordFail(
        runner.runExecution,
        runner.currentShrinkable.value,
        runner.currentIdx)


proc execProperty*[T](
    name: string,
    arb: Arbitrary[T],
    check: Predicate[T],
    params: AssertParams = defAssertPropParams()
  ): RunExecution[T] =
  ## Execute property using values generated by `arb`. Either run
  ## `params.runsNeforeSuccess`, or until first failure is found, returning
  ## execution results and associated metadata.


  var property = newProperty(arb, check)
  var runner = newRunner[T](name, params, arb)
  var pathSkip = if params.path.isSome(): params.path.get() else: @[]
  var pathPos = 0

  for item in items(runner):
    if params.runsBeforeSuccess.uint < runner.runExecution.runId.uint:
      break

    elif 0 < pathSkip.len and 1 < pathSkip[pathPos]:
      dec pathSkip[pathPos]
      continue

    let runStatus = property.run(item.value.value)
    runner.handleResult(runStatus)
    # QUESTION where to call and store shrinked values after failure has
    # been recorded?

  return runner.runExecution


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
    arb = arbTuple[A,B](arb1, arb2)
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
    arb = arbTuple[A,B,C](arb1, arb2, arb3)
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
