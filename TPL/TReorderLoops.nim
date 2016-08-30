import macros
import debug,utils
macro reorderLoops*(n: typed): untyped =
  dbg "reorderLoops <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    # echo "\n>>>> reorderLoops:g <= ", n.treerepr
    if n.kind == nnkForStmt:
      result = n
      result[^1] = n[^1].g
      # echo result.treerepr
      if result[^1].kind == nnkForStmt and
         result[^1][^2].kind in CallNodes and
         $result[^1][^2][0] == "indices" and
         result[^1][^2][2].kind == nnkIntLit and
         result[^1][^2][3].kind == nnkIntLit and
         result[^1][^2][2].intval > result[^1][^2][3].intval and
         result[^2].kind in CallNodes and
         $result[^2][0] in ["indices", "tail"] and
         result[^2][2].kind == nnkIntLit and
         result[^2][3].kind == nnkIntLit and
         result[^2][2].intval <= result[^2][3].intval:
        var
          loop = result[^1]
          inner = loop[^1]
        loop[^1] = result
        loop[^1][^1] = inner
        result = loop
    elif n.kind in StmtNodes:
      result = newStmtList()
      for c in n:
        result.add c.g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    else:
      result = n
  result = n.g
  dbg "reorderLoops => ", result, TPLDebug.detail
