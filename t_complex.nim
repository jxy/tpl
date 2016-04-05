import math
import tpl

tensorOps:
  var
    x, y, z: Tensor([Complex], float)
  x = sqrt 0.5
  y = x
  z = x * y
  echo "x = sqrt 0.5 = ", x
  echo "y = x = ", y
  echo "z = x * y = ", z
  z = x * y * z
  echo "z = x * y * z = ", z
  z = x * x * x * x * x * x * x * x
  echo "z = x * x * x * x * x * x * x * x = ", z
  
