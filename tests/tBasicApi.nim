import npbt

let runStats = execProperty(
  "manual",
  arbInt(0, 100),
  proc(c: int): PTStatus = asStatus(c < 10),
  propParams(1631815559, @[2])
)

echo $runStats
