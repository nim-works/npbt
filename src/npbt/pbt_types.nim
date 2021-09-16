import std/[options, mersenne]

from std/math import floor, log10

type
  PTStatus* = enum
    ## the result of a single run/predicate check
    ## XXX: likely to be changed to a variant to support, true/false/error+data
    ptPreCondFail
    ptFail
    ptPass

  RunId* = range[1..high(int)]
    ## sequential id of the run, starts from 1

  PossibleRunId* = int
   ## separate from `RunId` to support 0 value, indicating non-specified

  Predicate*[T] = proc(s: T): PTStatus
    ## test function to see if a property holds

  Random* = object
    ## random number arbitrary, allows abstraction over algorithm
    seed: uint32
    rng: MersenneTwister
    calls: uint          ## number of calls

  ArbitraryKind* = enum
    akLarge,     ## infeasilbe to generate all possible values (most cases)
    akExhaustive ## possible to generate all values (bool, enums, 8 bit ints)

  ArbitraryImpl[T] = proc(
    a: Arbitrary[T], mrng: var Random): Shrinkable[T]

  ShrinkImpl[T] = proc(value: Shrinkable[T]): seq[Shrinkable[T]]



  Arbitrary*[T] = object
    ## arbitrary value arbitrary for some type T
    ## XXX: eventually migrate to concepts once they're more stable, but
    ##      language stability is the big reason for making this whole property
    ##      based testing framework.
    mgenerate: ArbitraryImpl[T]
    shrink: ShrinkImpl[T]
    kind: ArbitraryKind # XXX: setup support for exhaustive kinds

  Shrinkable*[T] = object
    ## future support for shrinking
    value*: T

  Property*[T] = object
    ## a condition that must hold for an arbitrary as specified by a predicate
    arb: Arbitrary[T]
    predicate: Predicate[T]

  Frequency* = int
    ## future use to allow specification of biased generation

#-- Run Id

const noRunId* = 0.PossibleRunId

proc isUnspecified*(r: PossibleRunId): bool =
  ## used for default param handling
  result = r.uint == 0

proc newRun*(): RunId = 1.RunId

proc startRun*(r: var RunId): RunId {.discardable, inline.} =
  ## marks the current run as complete and returns the preivous RunId
  result = r
  inc r

proc startRun*(r: var PossibleRunId) {.inline.} =
  inc r

proc runIdToFrequency*(r: RunId): int =
  2 + toInt(floor(log10(r.int.float)))

#-- Shrinkable

# These seem redundant with Arbitraries, this is mostly for convenience. The
# main reason is that these represent map/filter/etc over a singular shrinkable
# valid value -- which might need particular care. The convenience is when we
# actually implement shrinking and distinguishing specific valid instance vs
# intermediate values an Arbitrary might generate along the way to generating a
# valid value are not the same thing.

proc map*[T, U](s: Shrinkable[T], mapper: proc(t: T): U): Shrinkable[U] =
  result = Shrinkable[U](value: mapper(s.value))

proc filter*[T](s: Shrinkable[T], predicate: proc(t: T): bool): Shrinkable[T] =
  result = Shrinkable[T](value: predicate(s.value))

proc shrinkableOf*[T](v: T): Shrinkable[T] =
  result = Shrinkable[T](value: v)

proc shrinkableOf*[T](v: var T): var Shrinkable[T] =
  result = Shrinkable[T](value: v)

proc asShrinkable*[T](v: sink T): Shrinkable[T] =
  ## Construct new shinkable entry, copying value
  Shrinkable[T](value: v)


#-- Arbitrary

proc generate*[T](a: Arbitrary[T], mrng: var Random): Shrinkable[T] =
  ## calls the internal implementation
  a.mgenerate(a, mrng)

proc arbitrary*[T](
    mgenerate: ArbitraryImpl[T],
    shrink: ShrinkImpl[T] = nil,
    kind: ArbitraryKind = akLarge
  ): Arbitrary[T] =

  Arbitrary[T](mgenerate: mgenerate, shrink: shrink, kind: kind)

proc map*[T,U](o: Arbitrary[T], mapper: proc(t: T): U): Arbitrary[U] =
  ## creates a new Arbitrary with mapped values
  ## XXX: constraining U by T isn't possible right now, need to fix generics
  var orig = o
  arbitrary() do (a: Arbitrary[U], mrng: var Random) -> Shrinkable[U]:
    orig.generate(mrng).map(mapper)

proc filter*[T](o: Arbitrary[T], predicate: proc(t: T): bool): Arbitrary[T] =
  ## creates a new Arbitrary with filtered values, aggressive filters can lead
  ## to exhausted values.
  var orig = o
  arbitrary() do (a: Arbitrary[T], mrng: var Random) -> Shrinkable[T]:
    result = a.generate(mrng)
    while not result.filter(predicate):
      result = result.generate(mrng)

proc flatMap*[T, U](s: Arbitrary[T],
                   fmapper: proc(t: T): Arbitrary[U]): Arbitrary[U] =
  ## creates a new Arbitrary for every value produced by `s`. For when you want
  ## to make the value of an Arbitrary depend upon the value of another.
  var orig = s
  arbitrary() do (a: Arbitrary[U], mrng: var Random) -> Shrinkable[U]:
    fmapper(orig.generate(mrng).value).generate(mrng)

proc take*[T](a: Arbitrary[T], n: uint, mrng: var Random): Shrinkable[seq[T]] =
  ## generates a sequence of values meant to be used collectively
  var rng = mrng
  result = shrinkableOf(newSeqOfCap[T](n))
  for i in 0..<n:
    result.value.add a.generate(rng).value
  mrng = rng

proc sample*[T](a: Arbitrary[T], n: uint, mrng: var Random): seq[Shrinkable[T]] =
  ## generate a sequence of values meant to be used individually
  var rng = mrng
  result = newSeqOfCap[Shrinkable[T]](n)
  for i in 0..<n:
    result.add a.generate(rng)
  mrng = rng

#-- Random Number Arberation
# XXX: the trick with rngs is that the number of calls to them matter, so we'll
#      have to start tracking number of calls in between arbitrary generation
#      other such things (well beyond just the seed) in order to quickly
#      reproduce a failure. Additionally, different psuedo random number
#      generation schemes are required because they have various distribution
#      and performance characteristics which quickly become relevant at scale.
proc newRandom*(seed: uint32 = 0): Random =
  Random(seed: seed, rng: newMersenneTwister(seed))

proc nextUint32*(r: var Random): uint32 =
  inc r.calls
  result = r.rng.getNum()

proc nextInt*(r: var Random): int =
  inc r.calls
  result = cast[int32](r.rng.getNum())

proc nextUint32*(r: var Random; min, max: uint32): uint32 =
  assert min < max, "max must be greater than min"
  let size = max - min
  result = min + (r.nextUint32() mod size)

proc nextInt*(r: var Random; min, max: int): int =
  assert min < max, "max must be greater than min"
  let size = abs(max - min)
  result = min + abs(r.nextInt() mod size)

#-- Property

converter toPTStatus(b: bool): PTStatus =
  ## yes, they're evil, but in this case they're incredibly helpful
  ## XXX: does this need to be exported?
  if b: ptPass else: ptFail

func asStatus*(b: bool): PTSTatus =
  ## Non-converter alternative to `toPTStatus`. Maybe converter should be
  ## exported, maybe not, but having simple proc for that purpose is
  ## useful.
  if b: ptPass else: ptFail

proc newProperty*[T](arb: Arbitrary[T], p: Predicate): Property[T] =
  result = Property[T](arb: arb, predicate: p)

proc withBias[T](arb: var Arbitrary[T], f: Frequency): var Arbitrary[T] =
  ## create an arbitrary with bias
  ## XXX: implement biasing
  return arb

proc toss(mrng: var Random) {.inline.} =
  ## skips 42 numbers to introduce noise between generate calls
  for _ in 0..41:
    discard mrng.nextInt()

proc generateAux[T](p: var Property[T], rng: Random,
                    r: PossibleRunId): Shrinkable[T] =
  var mrng = rng
  toss(mrng)
  result =
    if r.isUnspecified():
      p.arb.generate(mrng)
    else:
      p.arb.withBias(runIdToFrequency(r)).generate(mrng)

proc generate*[T](p: var Property[T], mrng: Random, runId: RunId): Shrinkable[T] =
  return generateAux(p, mrng, runId)

proc generate*[T](p: Property[T], mrng: Random): Shrinkable[T] =
  return generateAux(p, mrng, noRunId)

proc shrink*[T](p: Property[T], value: Shrinkable[T]): seq[Shrinkable[T]] =
  p.arb.shrink(value)

proc run*[T](p: Property[T], v: T): PTStatus =
  try:
    result = p.predicate(v)
  except:
    # XXX: do some exception related checking here, for now pass through
    raise getCurrentException()
  finally:
    # XXX: for hooks
    discard
