# Package

version       = "0.1.0"
author        = "haxscramper"
description   = "Nim property based testing"
license       = "Apache-2.0"
srcDir        = "src"


# Dependencies

requires "nim >= 1.4.8"

task docgen, "Generate documentation":
  exec "nim doc2 --project --warnings:off --outdir:htmldocs src/npbt.nim"
