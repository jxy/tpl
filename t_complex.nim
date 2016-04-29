import math
import unittest
import tpl

var
  x, y, z: Tensor([Complex], float)
test "complex multiplications":
  tensorOpsSilent:
    x = sqrt 0.5
    y = x
    echo "x = sqrt 0.5 = ", x
    echo "y = x = ", y
    check x.re == sqrt(0.5)
    check x.im == sqrt(0.5)
    check y.re == sqrt(0.5)
    check y.im == sqrt(0.5)
    y = x * y
    echo "y = x * y = ", y
    check y.re == 0
    check y.im == 1.0000000000000002
    z = x * x * x * x * x * x * x * x
    echo "z = x * x * x * x * x * x * x * x = ", z
    check z.re == 1.0000000000000002
    check z.im == 0
    z = (x * y - z) * x
    echo "z = (x * y - z) * x = ", z
    check z.re == -1.707106781186548
    check z.im == -0.7071067811865478
    z = y * ((x - z) * x - x * x)
    echo "z = y * ((x - z) * x - x * x) = ", z
    check z.re == -1.7071067811865481
    check z.im == 0.7071067811865478
    z = y * ((x * y - z) * x - x * x)
    echo "z = y * ((x * y - z) * x - x * x) = ", z
    check z.re == 0.2928932188134525
    check z.im == 0.7071067811865481
    z = y * ((x * y - z) * x - x * x) * (z - x) * x
    echo "z = y * ((x * y - z) * x - x * x) * (z - x) * x = ", z
    check z.re == -0.7071067811865483
    check z.im == -0.29289321881345187

test "complex vectors":
  tensorOpsSilent:
    I = IndexType(0,2)
    var
      v, u: Tensor([Complex, I], float)
      k = I.dummy
    v[k] = sqrt(k) * x
    u = x * v
    echo "v[k] = sqrt(k) * x = ", v
    check $v == """[[ 0.0               , 0.0                ],
 [ 0.7071067811865476, 0.7071067811865476 ],
 [ 1.0               , 1.0                ]]"""
    echo "u = x * v = ", u
    check $u == """[[ 0.0, 0.0               ],
 [ 0.0, 1.0               ],
 [ 0.0, 1.414213562373095 ]]"""
    v.im += sqrt 0.5
    u = x * v
    echo "v.im += sqrt 0.5; v = ", v
    check $v == """[[ 0.0               , 0.7071067811865476 ],
 [ 0.7071067811865476, 1.414213562373095  ],
 [ 1.0               , 1.707106781186548  ]]"""
    echo "u = x * v = ", u
    check $u == """[[ -0.5000000000000001, 0.5000000000000001 ],
 [ -0.5000000000000001, 1.5                ],
 [ -0.5000000000000002, 1.914213562373096  ]]"""
    echo "u.re = ", u.re
    check $u.re == "[ -0.5000000000000001, -0.5000000000000001, -0.5000000000000002 ]"
    u.im = v.im
    echo "u.im = v.im; u.im = ", u.im
    check $u.im == "[ 0.7071067811865476, 1.414213562373095, 1.707106781186548 ]"
