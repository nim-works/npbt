import npbt
from std/strformat import fmt
from std/times import toUnix

from macros import NimNodeKind



spec "nim":
  spec "uint32":
    forAll("are >= 0, yes it's silly ", arbUint32(),
           proc(i: uint32): PTStatus = asStatus(i >= 0))

    let
      min: uint32 = 100000000
      max = high(uint32)
    forAll(fmt"within the range[{min}, {max}]", arbUint32(min, max),
           proc(i: uint32): PTStatus = asStatus(i >= min and i <= max))

  spec "enums":
    forAll("are typically ordinals", arbEnum[NimNodeKind](),
           proc(n: NimNodeKind): PTStatus = asStatus(
               n > NimNodeKind.low  or n == NimNodeKind.low or
               n < NimNodeKind.high or n == NimNodeKind.high
           ))

  spec "characters":
    spec "are ordinals":
      forAll("forming a bijection with int values between 0..255 (inclusive)",
             arbChar(),
             proc(c: char): PTStatus =
               asStatus(c == chr(ord(c)) and ord(c) >= 0 and ord(c) <= 255))

      block:
        let gen = proc(c: char): (char, char, char) =
          let
            prev = if c == low(char): c else: pred(c)
            curr = c
            next = if c == high(char): c else: succ(c)
          (prev, curr, next)
        forAll("have successors and predecessors or are at the end range",
               arbChar().map(gen),
               proc(cs: (char, char, char)): PTStatus =
                 let (a, b, c) = cs
                 asStatus(
                   (a < b and b < c) or
                   (a <= b and b < c) or
                   (a < b and b <= c)))

    forAll("ascii - are from 0 to 127",
           arbCharAscii(),
           proc(c: char): PTStatus =
             asStatus(c.ord >= 0 or c.ord <= 127))

  spec "strings":
    forAll("concatenation - len is >= the sum of the len of the parts",
           arbString(), arbString(),
           proc(ss: (string, string)): PTStatus =
             let (a, b) = ss
             asStatus(a.len + b.len <= (a & b).len))

ctSpec "NimNode":
  forAll("generate NimNodes for no good reason",
          arbNimNode(),
          proc(n: NimNode): PTStatus = asStatus(true))

  when false:
    # XXX: Use this for debugging
    var rnd = newRandom(
      cast[uint32](clamp(toUnix(getTime()), 0'i64, uint32.high.int64)))

    for i in arbEnum().sample(10, rnd):
      echo i.value
