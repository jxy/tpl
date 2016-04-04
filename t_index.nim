import tpl
import unittest

proc main {.tensorOpsSilent.} =
  type
    I = IndexType(3)
    J = IndexType(1,2)
  var
    i = I.index 2
    j = J.index 1
  test "index i":
    echo i
    check(i == 2)
    i.index = 0
    echo i
    check(i == 0)
  test "index j":
    echo j
    check(j == 1)
    j = 2
    echo j
    check(j == 2)

main()
