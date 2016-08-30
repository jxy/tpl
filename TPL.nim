import macros

import TPL.tensor_data_default
export tensor_data_default.`[]`
export tensor_data_default.`[]=`

import TPL.debug
export debug.TPLDebug

import TPL.ops
export ops.dummy
export ops.Tensor
export ops.IndexType
export ops.index
export ops.`index=`
export ops.`[]`
export ops.`[]=`
export ops.TPLDummyConv
export ops.TPLIndexConv
export ops.staticForIndex
export ops.staticForStmt
export ops.items
export ops.`+`
export ops.`-`
export ops.`*`
export ops.`/`
export ops.`+=`
export ops.`-=`
export ops.`*=`
export ops.`/=`
export ops.tail
export ops.`$`

import TPL.TReAssign
import TPL.TConvertAutoDummy
import TPL.TAutoSum
import TPL.TLooping
import TPL.TReorderLoops
import TPL.TFusion
import TPL.TCleanup

macro withDbgLevel(verbose: static[TPLDebug], n: untyped): untyped =
  template g(v: TPLDebug, n: untyped): untyped =
    static:
      const OldLvl = TPLDebugLevel
      TPLDebugLevel = TPLDebug(v)
    n
    static:
      TPLDebugLevel = OldLvl
  result = getast g(verbose, n)
template tplHelper(v: TPLDebug, n: untyped): untyped =
  cleanup:
    withDbgLevel TPLDebug(v):
      showCallResult:
        fusion reorderLoops cleanup looping autoSum requireTemporary splitting convertAutoDummy reAssign n
proc tplWithDbgLevel(v: TPLDebug, n: NimNode): NimNode =
  if n.kind in RoutineNodes:
    result = n
    result[6] = getast tplHelper(v, n[6])
  else:
    result = getast tplHelper(v, n)
macro tpl*(n: untyped): untyped =
  result = tplWithDbgLevel(TPLDebug.final, n)
macro tplTrace*(verbose: static[TPLDebug], n: untyped): untyped =
  result = tplWithDbgLevel(verbose, n)
macro tplSilent*(n: untyped): untyped =
  result = tplWithDbgLevel(TPLDebug.none, n)

# conveniently import modules and export utilities
# that depend on the definition of `tpl`.

import TPL.extras
export TPL.extras.`$`