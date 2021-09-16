from std/sequtils import toSeq
from std/sugar import `=>`
from std/strutils import join
from std/macros import NimNodeKind, newNimNode

import ./pbt_types

proc tupleArb*[A](a1: Arbitrary[A]): Arbitrary[(A,)] =
  ## Arbitrary of single-value tuple
  result = Arbitrary[(A,)](
    mgenerate: proc(arb: Arbitrary[(A,)], rng: var Random): Shrinkable[(A,)] =
                  shrinkableOf((a1.generate(rng).value,))
  )

proc tupleArb*[A,B](a1: Arbitrary[A], a2: Arbitrary[B]): Arbitrary[(A,B)] =
  ## Arbitrary of pair tuple
  var
    o1 = a1
    o2 = a2
  result = Arbitrary[(A,B)](
    mgenerate: proc(a: Arbitrary[(A,B)], rng: var Random): Shrinkable[(A,B)] =
                  shrinkableOf(
                    (o1.generate(rng).value, o2.generate(rng).value)
                  )
  )

proc intArb*(): Arbitrary[int] =
  arbitrary() do (arb: Arbitrary[int], rng: var Random) -> Shrinkable[int]:
    shrinkableOf(rng.nextInt())

proc intArb*(min, max: int): Arbitrary[int] =
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

proc uint32Arb*(): Arbitrary[uint32] =
  arbitrary(
    proc(arb: Arbitrary[uint32], rng: var Random): Shrinkable[uint32] =
      shrinkableOf(rng.nextUint32())
  )

proc uint32Arb*(min, max: uint32): Arbitrary[uint32] =
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

proc charArb*(min, max: char): Arbitrary[char] =
  ## create a char arbitrary for a given range
  var
    vals = toSeq(min..max)
    pos: int = 0
  result = arbitrary(
    kind = akExhaustive,
    mgenerate = proc(arb: Arbitrary[char], rng: var Random): Shrinkable[char] =
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

proc charArb*(): Arbitrary[char] {.inline.} =
  ## create a char arbitrary for the full character range, see: `charAsciiArb`
  charArb(char.low, char.high)

proc charAsciiArb*(): Arbitrary[char] {.inline.} =
  ## create an ascii char arbitrary
  charArb(char.low, chr(127))

proc seqArbOf*[T](a: Arbitrary[T], min: uint32 = 0, max: uint32 = 100): Arbitrary[seq[T]] =
  ## create a sequence of varying size of some type
  assert min <= max
  result = uint32Arb(min, max).map((i) => a.take(i))

proc stringArb*(min: uint32 = 0, max: uint32 = 1000, charArb = charArb()): Arbitrary[string] =
  ## create strings using the full character range with len of `min` to `max`
  ## see: `stringAsciiArb`
  result = arbitrary() do (a: Arbitrary[string], mrng: var Random) -> Shrinkable[string]:
    let size = mrng.nextUint32(min, max)
    charArb.take(size, mrng).map((cs) => cs.join())

proc stringAsciiArb*(min: uint32 = 0, max: uint32 = 1000): Arbitrary[string] {.inline.} =
  ## create strings using the ascii character range with len of `min` to `max`
  stringArb(min, max, charAsciiArb())

proc enumArb*[T: enum](): Arbitrary[T] =
  # XXX: use a uint32 arb to get a value between the current pos and end of seq, then swap access over that
  var
    vals = toSeq(T.low..T.high)
    pos: int = 0
  result = arbitrary(
    kind = akExhaustive,
    mgenerate = proc(arb: Arbitrary[T], rng: var Random): Shrinkable[T] =
                  let
                    endPos = max(0, vals.len - 1)
                    atEnd = pos == endPos
                    swapPos = if atEnd: endPos
                              else: rng.nextInt(pos, endPos)
                  result = shrinkableOf(vals.swapAccess(pos, swapPos))
                  inc pos
                  if pos == endPos:
                    pos = 0
  )

proc nimNodeArb*(): Arbitrary[NimNode] =
  # XXX: what is even going on?
  result = enumArb[NimNodeKind]().map(k => newNimNode(k))
