import std/[strutils, tables]

from std/sequtils import toSeq
from std/sugar import `=>`
from std/macros import NimNodeKind, newNimNode, nnkRequireInitKinds
from std/unicode import Rune, `$`
from std/strformat import `&`

import ./pbt_types

proc getFirst*[T](
    a: Arbitrary[T],
    getN: int = 8,
    random: Random = newRandom()): seq[T] =

  var rand = random
  for i in 0 ..< getN:
    result.add a.generate(rand).value

type
  CollectionGenFlags = enum
    ## Configuration flags for arbitraries that generate collections of
    ## values. Describes different strategies and constraints for
    ## arbitraries. Usually paired with additional configuration options
    ## such as repeat chance, max number of repeats and so on.
    # REVIEW move these parameters into separate type as well?
    # REVIEW have separate flags for different kinds of configuration

    # Repeat enable/disable flags
    cgfAllowRepeat ## Allow repeated values in the generated sequence
    cgfRequireSomeRepeat ## Require at least some values to be repeated in
                         ## the generated collection
    cgfRequireAllRepeat ## Each generated value must be present at least
                        ## twice in the generated sequence

    cgfDisallowRepeat ## No value repetiton in genrated sequence is allowed

    # Rrepeat order configuration
    cgfSequentialRepeat ## Repeated values will be placed in sequence
                        ## things like `[a, a, b, c, c]` are allowed.
    cgfRandomizedRepeat ## Repeated values must not be placed in sequence.
                        ## If duplicate exists it will not be placed
                        ## together with the same item. `[a, b, a]` is
                        ## allowed but not `[a, a, b]`

const
  cgfRepeatEnableKinds* = { cgfAllowRepeat .. cgfDisallowRepeat }
  cgfRepeatOrderKinds* = { cgfSequentialRepeat .. cgfRandomizedRepeat }

func first[I](s: set[I]): I =
  assert len(s) > 0, "Cannot get first item from empty set"
  for i in s:
    return i




proc arbTuple*[A](a1: Arbitrary[A]): Arbitrary[(A,)] =
  ## Arbitrary of single-value tuple
  result = arbitrary(
    proc(arb: Arbitrary[(A,)], rng: var Random): Shrinkable[(A,)] =
      shrinkableOf((a1.generate(rng).value,))
  )

proc arbTuple*[A,B](a1: Arbitrary[A], a2: Arbitrary[B]): Arbitrary[(A,B)] =
  ## Arbitrary of pair tuple
  var
    o1 = a1
    o2 = a2
  result = arbitrary(
    proc(a: Arbitrary[(A,B)], rng: var Random): Shrinkable[(A,B)] =
      shrinkableOf((o1.generate(rng).value, o2.generate(rng).value))
  )

proc arbInt*(): Arbitrary[int] =
  ## Create int arbitrary generator with values with full range of integer
  ## values
  arbitrary() do (arb: Arbitrary[int], rng: var Random) -> Shrinkable[int]:
    shrinkableOf(rng.nextInt())

proc arbInt*(min, max: int): Arbitrary[int] =
  ## create a int arbitrary with values in the range of min and max which are
  ## inclusive.
  arbitrary(
    proc(arb: Arbitrary[int], rng: var Random): Shrinkable[int] =
      shrinkableOf(rng.nextInt(min, max)),
    proc(value: Shrinkable[int]): seq[Shrinkable[int]] =
      var value = value.value
      while min < value:
        result.add asShrinkable(value)
        value = min + int((value - min) / 2)

  )

proc arbuint32*(): Arbitrary[uint32] =
  arbitrary(
    proc(arb: Arbitrary[uint32], rng: var Random): Shrinkable[uint32] =
      shrinkableOf(rng.nextUint32())
  )

proc arbuint32*(min, max: uint32): Arbitrary[uint32] =
  ## create a uint32 arbitrary with values in the range of min and max which
  ## are inclusive.
  arbitrary(
    proc(arb: Arbitrary[uint32], rng: var Random): Shrinkable[uint32] =
      shrinkableOf(rng.nextUint32(min, max))
  )

proc swapAccess[T](s: var openArray[T], a, b: int): T =
  ## swap the value at position `a` for position `b`, then return the new value
  ## at position `a`. Used for exhaustive arbitrary traversal.
  result = s[b]

  if a != b:      # only need to swap if they're different
    s[b] = s[a]
    s[a] = result

proc arbSeq*[A](
    itemArb: Arbitrary[A],
    minLen: Natural,
    maxLen: Natural,
    flags: set[CollectionGenFlags] = { cgfAllowRepeat, cgfSequentialRepeat }
  ): Arbitrary[seq[A]] =
  ## Construct arbitrary sequence of items with specified lenght ranges
  ##
  ## - @arg{seqLenRange} :: Min and max number of elements in the generated
  ##   sequence.
  ## - @arg{flags} :: Configuration for ordering and repeat strategies. For
  ##   more information see [[code:CollectionGenFlags]]

  let repeatKinds = flags * cgfRepeatEnableKinds
  assert len(repeatKinds) == 1,
    "Only one repeat strategy can be used at a time, but " &
    &"{repeatKinds} specified"

  let repeatOrder = flags * cgfRepeatOrderKinds
  assert len(repeatOrder) == 1,
    "Only one repeat ordering can be used at a time, but " &
    &"{repeatKinds} specified"

  let order = repeatOrder.first()
  let kinds = repeatKinds.first()
  let newLen = arbInt(minLen, maxLen)

  var genCount: Table[A, int] # Hate count tables, so using regular ones
  result = arbitrary() do (
      a: Arbitrary[seq[A]], r: var Random) -> Shrinkable[seq[A]]:

    var res: seq[A]
    let targetLen = newLen.getValue(r)
    case kinds:
      of cgfAllowRepeat:
        while len(res) < targetLen:
          res.add itemArb.getValue(r)

      else:
        assert false, $kinds

    return asShrinkable(res)



proc arbSample*[T](values: seq[T]): Arbitrary[T] =
  var
    vals = values
    pos: int = 0

  result = arbitrary(
    kind = akExhaustive,
    mgenerate = proc(arb: Arbitrary[T], rng: var Random): Shrinkable[T] =
                  let
                    endPos = vals.len - 1
                    atEnd = pos == endPos
                    swapPos = if atEnd: endPos
                              else: rng.nextInt(pos, endPos)
                  result = shrinkableOf(vals.swapAccess(pos, swapPos))
                  inc pos
                  if pos == endPos:
                    pos = 0
  )

proc arbChar*(chars: set[char]): Arbitrary[char] =
  ## create a char arbitrary for a given range
  arbSample(toSeq(chars))

proc arbChar*(min, max: char): Arbitrary[char] =
  ## create a char arbitrary for a given range
  arbSample(toSeq(min .. max))

proc arbChar*(): Arbitrary[char] {.inline.} =
  ## create a char arbitrary for the full character range, see: `arbcharAscii`
  arbChar(char.low, char.high)

proc arbCharAscii*(): Arbitrary[char] {.inline.} =
  ## create an ascii char arbitrary
  arbChar(char.low, chr(127))

proc arbSeqOf*[T](a: Arbitrary[T], min: uint32 = 0, max: uint32 = 100): Arbitrary[seq[T]] =
  ## create a sequence of varying size of some type
  assert min <= max
  result = arbuint32(min, max).map((i) => a.take(i))

proc arbString*(
    min: uint32 = 0, max: uint32 = 1000, arbchar = arbchar()
  ): Arbitrary[string] =
  ## create strings using the full character range with len of `min` to `max`
  ## see: `arbstringAscii`
  result = arbitrary() do (
      a: Arbitrary[string], mrng: var Random) -> Shrinkable[string]:
    let size = mrng.nextUint32(min, max)
    arbChar.take(size, mrng).map((cs) => cs.join())

proc arbRune*(): Arbitrary[Rune] =
  let arbValues = arbUInt32(0, high(uint32))
  arbitrary() do (a: Arbitrary[Rune], r: var Random) -> Shrinkable[Rune]:
    shrinkableOf Rune(arbValues.generate(r).value)

proc arbStringNimIdent*(
    idLen: int = 12,
    repeatNormalized: bool = false,
    useUnicode: bool = false
  ): Arbitrary[string] =
  ## Generate arbitrary nim identifiers, including upper/lower cased ones,
  ## with underscore separation etc.
  ## - @arg{repeatNormalized} :: Allow generator to produce identifiers with
  ##   identical normalied values (nim identifier normalization)
  ##
  ## - TODO :: implement unicode support


  let leadChar = arbChar(IdentStartChars)
  let bodyChar = arbChar(IdentChars)
  let bodyAlnum = arbChar({'a' .. 'z', 'A' .. 'Z', '0' .. '9'})
  var normalizedYield: Table[string, bool]

  proc nimNorm(s: string): string =
    result.add s[0]
    for ch in s[1..^1]:

      case ch:
        of 'a' .. 'z' : result.add ch
        of '_' : discard
        of 'A' .. 'Z': result.add char(ch.uint8 - ('A'.uint8 - 'a'.uint8))
        else: result.add ch

  arbitrary() do (
    a: Arbitrary[string], r: var Random) -> Shrinkable[string]:
    var foundNext = false
    var res: string
    while not foundNext:
      res = ""
      while res.len < idLen:
        if res.len == 0:
          res.add leadChar.getValue(r)

        else:
          if res[^1] in {'_'}:
            res.add bodyAlnum.getValue(r)

          else:
            res.add bodyChar.getValue(r)

      foundNext = repeatNormalized or res.nimNorm() notin normalizedYield
      if not repeatNormalized:
        normalizedYield[res] = true


    return asShrinkable(res)

proc arbStringAscii*(
    min: uint32 = 0, max: uint32 = 1000): Arbitrary[string] {.inline.} =
  ## create strings using the ascii character range with len of `min` to `max`
  arbstring(min, max, arbcharAscii())

proc arbEnum*[T: enum](values: set[T] = {low(T) .. high(T)}): Arbitrary[T] =
  ## Create arbitrary enum generator using set of allowed values
  # XXX: use a uint32 arb to get a value between the current pos and end of
  # seq, then swap access over that
  arbSample(toSeq(values))
  # var
  #   vals = toSeq(values)
  #   pos: int = 0

  # result = arbitrary(
  #   kind = akExhaustive,
  #   mgenerate = proc(arb: Arbitrary[T], rng: var Random): Shrinkable[T] =
  #     let
  #       endPos = max(0, vals.len - 1)
  #       atEnd = pos == endPos
  #       swapPos = if atEnd: endPos
  #                 else: rng.nextInt(pos, endPos)
  #     result = shrinkableOf(vals.swapAccess(pos, swapPos))
  #     inc pos
  #     if pos == endPos:
  #       pos = 0
  # )

proc arbNimNode*(): Arbitrary[NimNode] =
  ## create an arbitrary NimNode
  const
    arbAbleNodes =
      {NimNodeKind.low .. NimNodeKind.high} - nnkRequireInitKinds
  result = arbEnum[NimNodeKind](arbAbleNodes).map(k => newNimNode(k))
