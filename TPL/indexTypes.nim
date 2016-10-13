import macros
import seqdict

####################
# index type
type
  # Ideally `AnyIndex` would be a type class to simply the
  # complexity of defining indexing procedures with all the
  # possible index types (O(e^n) definitions for rank-n tensor if
  # defined separately for each index type).  The type class of
  # generic types does not work reliably in Nim now, so we use an
  # extra static type parameters to differentiate different index
  # types, while maintaining the ability to refer to all the
  # index types with this generic type.
  # FIXME: since v0.14, unused generic type parameter no longer
  # distinguish types, we need to design a new type that works
  # with macro indexer.
  AnyIndex*[ty:static[TPLIndex],id,lo,hi:static[int]] = object {.requiresInit.}
    # `ty` is the type of the index.
    # `value` auto inits to 0, which is bad
    # `requiresInit` in v0.13 gives warning without an explicit initialization
    value*: int
  TPLIndex* {.pure.} = enum
    raw, index, dummy
type
  gTindexUninitialized*[id,lo,hi:static[int]] = AnyIndex[TPLIndex.raw,id,lo,hi]
  gTindex*[id,lo,hi:static[int]] = AnyIndex[TPLIndex.index,id,lo,hi]
converter TPLIndexConv*[id,lo,hi:static[int]](i: AnyIndex[TPLIndex.index,id,lo,hi]): int = i.value
converter TPLIndexConv*[id,lo,hi:static[int]](i: AnyIndex[TPLIndex.index,id,lo,hi]): float = i.value.float

var IndexLength {.compileTime.} = newseqdict[int, NimNode]()
macro savedIndexLength(n: static[int]): untyped =
  result = IndexLength[n]
template iterateIndices*(id, lo, hi, begin: static[int]): untyped =
  const
    cid = id
    clo = lo
    chi = hi
  when chi < clo:               # A variable length index.
    let
      n = savedIndexLength(cid)
    when declared(threadNum) and declared(numThreads):
      let
        cbegin = begin + ((threadNum*n) div numThreads)
        cend = begin + (((threadNum+1)*n) div numThreads) - 1
      #echo "thread #", threadNum, ": ", cbegin, " - ", cend
    else:
      let
        cbegin = begin
        cend = begin + n - 1
    if cbegin <= cend:
      var i = gTindex[cid,clo,chi](value: cbegin)
      while true:
        yield i
        if i.value == cend: break
        inc i.value
  else:
    when begin <= chi:
      var i = gTindex[cid,clo,chi](value: begin)
      while true:
        yield i
        if i.value == chi: break
        inc i.value
template iterateIndices*(id, lo, hi: static[int]): untyped =
  iterateIndices(id, lo, hi, lo)
iterator indices*(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  iterateIndices(id, lo, hi)
iterator items*[ty:static[TPLIndex];id,lo,hi:static[int]](t: typedesc[AnyIndex[ty,id,lo,hi]]): gTindex[id,lo,hi] =
  iterateIndices(id, lo, hi)

proc `$`*[id,lo,hi:static[int]](x: AnyIndex[TPLIndex.index,id,lo,hi]): string =
  when hi < lo:
    $x.value & ":IdxV[" & $id & "," & $lo & "," & $(savedIndexLength(id)+lo-1) & "]"
  else:
    $x.value & ":Idx[" & $id & "," & $lo & "," & $hi & "]"

template uninitializedIndex(t: untyped, id, lo, hi: static[int]): expr =
  const
    ci = id
    cl = lo
    ch = hi
  type t = gTindexUninitialized[ci, cl, ch]
macro indexTypeStatic(t: untyped, id, lo, hi: static[int]): untyped =
  if hi < lo:
    error "IndexType got upper bound: " & $hi & ", lower than the lower bound: " & $lo
  result = newCall(bindsym"uninitializedIndex", t, id.newlit, lo.newlit, hi.newlit)
  # echo "indexTypeStatic: ",  result.repr
macro indexTypeVar(t: untyped, id, lo: static[int], hi: int): untyped =
  let vlen = gensym(nskVar, "__varIndexLength__" & $id & "__" & $lo)
  result = newNimNode(nnkStmtListExpr).add(
    newNimNode(nnkVarSection).add(
      newIdentDefs(
        newNimNode(nnkPragmaExpr).add(vlen, newNimNode(nnkPragma).add(ident"global")),
        ident"int")),
    newAssignment(vlen, infix(infix(hi, "-", lo.newlit), "+", 1.newlit)),
    newCall(bindsym"uninitializedIndex", t, id.newlit, lo.newlit, (lo - 1).newlit))
  IndexLength.add(id, vlen)
  # echo "indexTypeVar: ", result.repr
  # echo IndexLength.repr
template genIndexType(t: untyped, id, lo, hi: int): expr =
  when compiles((const x = hi)):
    indexTypeStatic(t, id, lo, hi)
  else:
    indexTypeVar(t, id, lo, hi)
var IndexID {.compileTime.} = 0
macro newIndexID: untyped =
  result = IndexID.newlit
  # echo "######## newIndexID: ", result.repr
  inc IndexID
template IndexTypeDef*(t, lo, hi: untyped): expr =
  # echo "IndexType: <= ", lo.repr, ", ", hi.repr
  genIndexType(t, newIndexID(), lo, hi)
template IndexTypeDef*(t, size: untyped): expr =
  # echo "IndexType: <= ", size.repr
  IndexTypeDef(t, 0, size - 1)

template staticInbound(n, lo, hi: static[int]): expr =
  static:
    when hi < lo:
      when n < lo:
        error "index, " & $n & ", lower than the lower bound: " & $lo
    else:
      when n < lo or n > hi:
        error "index, " & $n & ", out of bounds [" & $lo & "," & $hi & "]"

proc indexValue*[id,lo,hi:static[int]](ix: AnyIndex[TPLIndex.index,id,lo,hi]): int {.inline.} = ix.value

proc index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:typedesc[AnyIndex[ty,id,lo,hi]], n:static[int]): gTindex[id,lo,hi] {.inline.} =
  n.staticInbound lo, hi
  result = type(result)(value: n)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:typedesc[AnyIndex[ty,id,lo,hi]]): expr =
  index(t, lo)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:AnyIndex[ty,id,lo,hi]): expr =
  index(type(t), lo)
template index*[ty:static[TPLIndex];id,lo,hi:static[int]](t:AnyIndex[ty,id,lo,hi], n:static[int]): expr =
  index(type(t), n)

proc `index=`*[id,lo,hi:static[int]](ix:var AnyIndex[TPLIndex.index,id,lo,hi], n:static[int]) {.inline.} =
  n.staticInbound lo, hi
  ix.value = n

macro nthIndex*(n: static[int], ixnums: varargs[int]): untyped =
  # echo "nthIndex <= ", $n, ", ", ixnums.repr
  if n >= 0 and n < ixnums.len div 3:
    result = newNimNode(nnkBracketExpr).add bindsym"gTindex"
    for i in 3*n .. 3*n+2:
      # echo i
      result.add ixnums[i]
  else:
    error "Index number, " & $n & ", out of range [0," & $(ixnums.len div 3 - 1) & "]"
  # echo "nthIndex => ", result.lisprepr

####################
# dummy index type
type
  gTindexDummy*[id,lo,hi:static[int]] = AnyIndex[TPLIndex.dummy,id,lo,hi]
converter TPLDummyConv*[id,lo,hi:static[int]](i: AnyIndex[TPLIndex.dummy,id,lo,hi]): gTindex[id,lo,hi] {.nodecl.} = index(i)
converter TPLDummyConv*[id,lo,hi:static[int]](i: AnyIndex[TPLIndex.dummy,id,lo,hi]): int {.nodecl.} = discard
converter TPLDummyConv*[id,lo,hi:static[int]](i: AnyIndex[TPLIndex.dummy,id,lo,hi]): float {.nodecl.} = discard
proc dummyFromConverter*(n: NimNode): NimNode =
  # echo "dummyFromConverter: <= ", n.lisprepr
  if n.kind in CallNodes and n[0].kind == nnkSym and n[0].eqIdent("TPLDummyConv"):
    let
      f = n[0].symbol.getimpl
      t = f[3][1][1]
    # echo "call type: ", n[0].gettype.lisprepr
    # echo "call Impl:\n", f.treerepr
    if f.kind == nnkConverterDef and
       ((t[0] == bindsym"AnyIndex" and
         ((t[1].kind == nnkIntLit and t[1].intval == int(TPLIndex.dummy)) or
          (t[1].kind == nnkSym and $t[1] == "dummy") # can't bindsym"dummy", other safer way?
         )
        ) or
        t[0] == bindsym"gTindexDummy"):
      result = n[1]
    else:
      error "dummyFromConverter got:\n" & n.treerepr & "\nwith f:\n" & f.repr & "\nparameter type: " & t.lisprepr
  elif n.kind in CallNodes and n[0].kind == nnkSym and n[0].eqIdent("indexValue"):
    let n1 = n[1]
    if n1.kind in CallNodes and n1[0].kind == nnkSym and n1[0].eqIdent("tail"):
      # echo n1[0].symbol.getimpl.treerepr
      let t = n1[0].symbol.getimpl[3][1][1]
      # echo t.treerepr
      if t[0] == bindsym"gTindexDummy" or
         (t[0] == bindsym"AnyIndex" and $t[1] == "dummy"):
        result = n[1]
      else:
        error "dummyFromConverter got:\n" & n.treerepr & "\nwith parameter type: " & t.lisprepr
  # echo "dummyFromConverter: => ", result.lisprepr

proc dummy*[ty:static[TPLIndex];id,lo,hi:static[int]](t: typedesc[AnyIndex[ty,id,lo,hi]]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)
proc dummy*[ty:static[TPLIndex];id,lo,hi:static[int]](t: AnyIndex[ty,id,lo,hi]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)
proc dummyIx*(id,lo,hi: static[int]): gTindexDummy[id,lo,hi] =
  result = type(result)(value: lo)

iterator items*[id,lo,hi:static[int]](t: AnyIndex[TPLIndex.dummy,id,lo,hi]): gTindex[id,lo,hi] =
  iterateIndices(id, lo, hi)
template head*[id,lo,hi:static[int]](t: AnyIndex[TPLIndex.dummy,id,lo,hi]): gTindex[id,lo,hi] =
  # This `index` call is also a template that gets expanded
  # leaving no trace of the variable `t`.
  index(t, lo)
iterator tail*(id, lo, hi: static[int]): gTindex[id,lo,hi] =
  iterateIndices(id, lo, hi, lo + 1)
proc tail*[id,lo,hi:static[int]](t: AnyIndex[TPLIndex.dummy,id,lo,hi]): gTindexDummy[id,lo,hi] {.nodecl.} = t

# template index*[id,lo,hi:static[int]](d:AnyIndex[TPLIndex.dummy,id,lo,hi], n:static[int]): expr =
  # index(gTindex[id,lo,hi], n)
