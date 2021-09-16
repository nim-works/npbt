import npbt

let runStats = execProperty(
  "manual",
  intArb(0, 100),
  proc(c: int): PTStatus = asStatus(c < 10)
)
