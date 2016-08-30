import macros
import debug,utils,indexTypes,ops
proc rebindAssignment(n: NimNode): NimNode =
  template g(la, lb, rhs): untyped =
    when compiles(`lb =`(la, rhs)):
      `lb =`(la, rhs)
    else:
      autoIndexAsgn(la.lb, rhs)
  if n.kind == nnkAsgn:
    if n[0].kind == nnkDotExpr:
      result = getast g(n[0][0], n[0][1], n[1])
    elif n[1].kind in CallNodes and $n[1][0] == "IndexType":
      result = newCall(bindsym"IndexTypeDef", n[0])
      for i in 1..<n[1].len:
        result.add n[1][i]
    else:
      result = newCall(bindsym"autoIndexAsgn", n[0], n[1])
  else:
    result = n
macro reAssign*(n: untyped): untyped =
  dbg "reAssign <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    if n.kind in StmtNodes:
      result = newStmtList()
      for i in 0..<n.len:
        result.add n[i].g
    elif n.kind in CallNodes:
      result = n
      for i in 1..<n.len:
        result[i] = n[i].g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind in {nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection}:
      result = n
    else:
      result = n.rebindAssignment
  result = n.g
  dbg "reAssign => ", result, TPLDebug.detail
