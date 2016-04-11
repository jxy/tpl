import math
import unittest
import tpl

var
  x, y, z: Tensor([Complex], float)
test "complex multiplications":
  tensorOps:
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
