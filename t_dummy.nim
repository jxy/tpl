import math
import tpl

type
  Spin = IndexType(1,4)
  Color = IndexType(1,4)
block:
  echo "\n* test index types"
  assert(not(Spin is Color), "Spin shouldn't be the same as Color")
  var
    s: Spin
    # The following 3 are syntactically equivalent
    # ss = 5.index(Spin)            # compile time error: out of bounds
    c = Color.index 2
    # c2 = index(Color,0)           # compile time error: out of bounds
  echo c
  c.index = 1
  echo c
  echo s, "  initialized to 0, which is bad, how can we check?"
  # s = Color.index(3)          # compile time error: wrong type
  # s = Spin.index(9)           # compile time error: out of bounds
  const
    one = 1
    two = 2
  s = Spin.index(two * one)
  echo s

block:
  echo "\n* test static and non static loops"
  var
    v, sv: Tensor(float, [Spin])
  echo "\n  * staticfor"
  # staticfor i, Color:         # compile time error: type mismatch
  #   sv[i] = i * 0.1 + 1.0
  staticfor i, Spin:
    sv[i] = i * 0.1 + 1.0
    echo "  [", i, "]: ", sv[i]
  echo "\n  * staticforstmt"
  staticforstmt:
    for i in Spin:
      v[i] += i * 10.0 - 10.0
      v[i] += 100.0
      echo "  [", i, "]: ", v[i]+`*`(2.0,sv[i])
      echo "  [", i, "]: ", v[i]+2.0*sv[i]
  echo "\n  * non static, but safe"
  for i in Spin:
    echo "  [", i, "]: ", sv[i]

block:
  echo "\n* test arithmatic with indices"
  type
    s2 = IndexType(3, 4)
    c3 = IndexType(0, 2)
  var
    scv: Tensor(float, [s2, c3])
  for j in c3:
    for i in s2:
      scv[i,j] = float i*10+j
      echo "[", i, ",", j, "]: ", scv[i,j]

block:
  var
    a, b: Dummy(Spin)
    x, y: Tensor(float, [Spin])
    m: Tensor(float, [Spin, Spin])
    mn: float
  echo "\n* test dummy"
  echo "\n  * test staticfor dummy"
  mn = 0
  staticfor i, a:
    m[i, Spin.index(2)] = (i-1.0)*0.1
    echo "  m[",i,",2] = ",m[i,Spin.index(2)]
    mn += m[i,i]
    echo "  mn = ", mn
  echo "\n  * test staticforstmt dummy"
  block:
    staticforstmt:
      for i in a:             # Dummy works as loop range
        m[i, Spin.index(1)] = (i-1.0)*1.0
        echo "  m[",i,",1] = ",m[i,Spin.index(1)]
  echo "\n  * test for dummy"
  block:
    for i in a:               # Dummy works as loop range
      m[i, Spin.index(1)] = m[i, Spin.index(1)] + 100.0
      echo "  m[",i,",1] = ",m[i,Spin.index(1)]
  echo "\n  * test auto loop dummy"
  tensorOps:
    m[a, b] = (a-1.0)*10.0/float(10^b)
    echo "  m =\n", m
    x[a] = if a == 1: 1.0 elif a == 2: 1e-2 elif a == 3: 1e-4 else: 1e-6
    # x[a] = 1.0*a
    # echo x[a]
    echo "  x = ", x
  echo "\n  * test auto sum"
  var
    c, d: a.type
    X, I: Tensor(float, [Spin, Spin])
  tensorOps:
    I[a,a] = 1.0
    echo "  I =\n", I
  tensorOps:
    mn = 0
    mn += I[a,b]*I[b,a]
    echo "  I_ab I_ba = ", mn
    X[a,b] = I[a,c]*m[c,b]
    echo "  X_ab = I_ac m_cb =\n", X
    mn = I[a,b]*m[b,a]
    echo "  I_ab m_ba = ", mn
    y[b] = m[a,b]
    echo "  y_b = m_ab = ", y
    x[a] = m[a,b]*y[b]
    echo "  x_a = m_ab y_b = ", x
    mn = m[a,b] * m[a,b]
    echo "  m.norm2 = ", mn
    X[a,b] = m[a,c]*I[c,a]
    echo "  X_ab = m_ac I_ca =\n", X
    X[a,b] = m[c,d]
    echo "  X_ab = m_cd =\n", X
  when false:
    x[a] = 1.0 + m[a,b]*y[b]
    echo "  x_a = m_ab y_b = ", x
    # X[a,b] = I[b,c]*x[c]*(m[c,d]*y[d])
    # echo "  X =\n", X
    # y[a] = m[a,b] * x[b] + x[a]
    # echo "  y = ", y

block:
  echo "\n* test nested"
  type
    inT = IndexType(0,1)
    In = Tensor(float, [inT])
    Color = IndexType(0,2)
    cm = Tensor(In, [Color, Color])
  var
    i: inT.Dummy
    mu, nu: Color.Dummy
    m: cm
  tensorOps:
    m[mu,nu][i] = 1.0*i*nu + 0.1*mu
    echo m
