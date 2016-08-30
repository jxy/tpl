import macros
type
  TPLDebug* {.pure.} = enum
    none, final, output, flow, detail
proc `$`(t: TPLDebug): string =
  case t
  of TPLDebug.none: "NONE"
  of TPLDebug.final: "FINAL"
  of TPLDebug.output: "OUTPUT"
  of TPLDebug.flow: "FLOW"
  of TPLDebug.detail: "DETAIL"
var
  TPLDebugLevel* {.compileTime.} = TPLDebug.final
proc dbg*(s: string = "", n: NimNode = newEmptyNode(), lvl: TPLDebug = TPLDebug.final) =
  if TPLDebugLevel >= lvl:
    let ns = if TPLDebugLevel >= TPLDebug.detail: n.treerepr else: n.repr
    echo "========================================"
    if n == newEmptyNode():
      echo "DBG:", lvl, ":", s
    else:
      echo "DBG:", lvl, ":", s, ns
macro showFinal(s: string, n: typed): untyped =
  dbg s.strval, n, TPLDebug.final
  result = n
macro showOutput(s: string, n: typed): untyped =
  dbg s.strval, n, TPLDebug.output
  result = n

import utils

macro showCallResult*(n: untyped): untyped =
  proc g(n: NimNode): NimNode =
    if n.kind in CallNodes and n.len == 2:
      result = n.copyNimNode
      result.add n[0]
      result.add n[1].g
      result = newCall(bindsym"showOutput", newlit($n[0] & " => "), result)
    elif n.kind in StmtNodes and n.len == 1 and n[0].kind in CallNodes:
      result = n[0].g
    else:
      result = n
  result = newCall(bindsym"showFinal", newLit" => ", n.g)
