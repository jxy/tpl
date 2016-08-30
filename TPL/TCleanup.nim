import macros
import debug,utils
macro cleanup*(n: typed): untyped =
  dbg "cleanup <= ", n, TPLDebug.flow
  proc g(n: NimNode): NimNode =
    # echo "\n>>>> cleanup:g <= ", n.treerepr
    if n.kind in StmtNodes:
      result = newStmtList()
      for c in n:
        # Skip varsection with the magic string.
        if c.kind == nnkVarSection and
           $c[0][0] == "__TPL__INTERNAL_REMOVE__":
          continue
        if c.kind == nnkDiscardStmt:
          continue
        if c.kind in StmtNodes: # Flatten out nested stmtlist.
          for cc in c.g:
            result.add cc
        else:
          result.add c.g
    elif n.kind == nnkBlockStmt:
      result = newBlockstmt(n[0], n[1].g)
    elif n.kind in RoutineNodes:
      result = n
      result[6] = n[6].g
    elif n.kind == nnkForStmt:
      result = n
      result[^1] = n[^1].g
    else:
      result = n
  result = n.g
  dbg "cleanup => ", result, TPLDebug.detail
