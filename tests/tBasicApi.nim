import npbt

var ctx = GlobalContext(specNames: @["manual"])
let report = execProperty(
  ctx, "manual",
  intArb(0, 100),
  proc(c: int): PTStatus = asStatus(c < 10)
)

for rep in report:
  echo rep
