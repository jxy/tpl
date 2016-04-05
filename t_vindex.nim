import tpl
import unittest

proc main {.tensorOpsSilent.} =
  var vlen = 4
  H = IndexType(1,5)
  I = IndexType(vlen)
  J = IndexType(1,vlen+1)
  K = IndexType(4)
  var
    h = H.index 5
    i = I.index 2
    j = J.index 1
    k = K.index 3
  test "index h":
    echo "h = ", h
    check(h == 5)
    check($h == "5:Idx[0,1,5]")
    h.index = 1
    echo "h = ", h
    check(h == 1)
    check($h == "1:Idx[0,1,5]")
  test "var index i":
    echo "i = ", i
    check(i == 2)
    check($i == "2:IdxV[1,0,3]")
    i.index = 0
    echo "i = ", i
    check(i == 0)
    check($i == "0:IdxV[1,0,3]")
  test "var index j":
    echo "j = ", j
    check(j == 1)
    check($j == "1:IdxV[2,1,5]")
    j = 2
    echo "j = ", j
    check(j == 2)
    check($j == "2:IdxV[2,1,5]")
  test "index k":
    echo "k = ", k
    check(k == 3)
    check($k == "3:Idx[3,0,3]")
    k = 0
    echo "k = ", k
    check(k == 0)
    check($k == "0:Idx[3,0,3]")

main()
