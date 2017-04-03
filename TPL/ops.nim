import macros,strutils
import utils,seqdict,debug,seqset

import indexTypes
export indexTypes.`$`
export indexTypes.`index=`
export indexTypes.index
export indexTypes.items
export indexTypes.TPLIndexConv
export indexTypes.dummy
export indexTypes.TPLDummyConv
export indexTypes.tail

import tensorTypes
export tensorTypes.Tensor
export tensorTypes.IndexType
export tensorTypes.`[]`
export tensorTypes.`[]=`

import XComplex


####################
# Automatic dummy index
# FIXME: only defined upto gT4 (exploring alternatives)
proc automaticIndex(id, lo, hi: static[int]): gTindexDummy[id,lo,hi] {.nodecl.} =
  dummyIx(id, lo, hi)

macro indexing(x: typed;
               ids: openarray[int];
               ixs: openarray[typed]; ixid: openarray[int];
               y: untyped = nil): untyped =
  let
    nrank = ids.len div 3
    nix = ixs.len
  if nix != ixid.len div 3:
    error "indexing got indices: " & ixs.repr & "\nwith ids: " & ixid.repr
  var
    match = newseq[seq[bool]](nix)
    total = newseq[int](nix)
    nsameIx = newseq[int](nix)
    nmatch = newseq[int](nrank)
  for i in 0..<nix:
    for j in (i+1)..<nix:
      if ixid[3*i] == ixid[3*j] and
         ixid[3*i+1] == ixid[3*j+1] and
         ixid[3*i+2] == ixid[3*j+2]:
        inc nsameIx[i]
        inc nsameIx[j]
  # echo nsameIx.repr
  for k in 0..<nrank:
    nmatch[k] = -1
  for h in 0..<nix:
    match[h].newseq(nrank)
    for k in 0..<nrank:
      match[h][k] = true
      for j in 0..2:
        match[h][k] = match[h][k] and ixid[3*h+j].intval == ids[3*k+j].intval
      if match[h][k]:
        inc total[h]
    if total[h] > 0 and total[h] != nsameIx[h] + 1:
      error "Ambiguous indexing for: " & x.repr & "[" & ixs[h].repr & "]"
    elif total[h] == 0:
      error "Indexing fails for: " & x.repr & "[" & ixs[h].repr & "]"
    else:
      for k in 0..<nrank:
        if match[h][k] and nmatch[k] < 0:
          nmatch[k] = h
          break
  if y == nil:
    result = newCall("[]", x)
  else:
    result = newCall("[]=", x)
  for k in 0..<nrank:
    if nmatch[k] >= 0:
      result.add ixs[nmatch[k]]
    else:
      var autoix = newCall(bindsym"automaticIndex")
      for j in 0..2:
        autoix.add ids[3*k+j]
      result.add autoix
  if y != nil:
    result.add y
  result = result.copy
  # echo result.treerepr
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: AnyIndex[i1ty,i1id,i1lo,i1hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2], [i1], [i1id, i1lo, i1hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2], [i1], [i1id, i1lo, i1hi], y)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT3[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3], i1: AnyIndex[i1ty,i1id,i1lo,i1hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3], [i1], [i1id, i1lo, i1hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT3[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3], [i1], [i1id, i1lo, i1hi], y)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1], [i1id, i1lo, i1hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi:static[int],i1ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1], [i1id, i1lo, i1hi], y)

template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,i1id,i1lo,i1hi,i2id,i2lo,i2hi:static[int],i1ty,i2ty:static[TPLIndex]](x: gT3[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3], [i1, i2], [i1id, i1lo, i1hi, i2id, i2lo, i2hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,i1id,i1lo,i1hi,i2id,i2lo,i2hi:static[int],i1ty,i2ty:static[TPLIndex]](x: gT3[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3], [i1, i2], [i1id, i1lo, i1hi, i2id, i2lo, i2hi], y)
template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi,i2id,i2lo,i2hi:static[int],i1ty,i2ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1, i2], [i1id, i1lo, i1hi, i2id, i2lo, i2hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi,i2id,i2lo,i2hi:static[int],i1ty,i2ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1, i2], [i1id, i1lo, i1hi, i2id, i2lo, i2hi], y)

template `[]`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi,i2id,i2lo,i2hi,i3id,i3lo,i3hi:static[int],i1ty,i2ty,i3ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi], i3: AnyIndex[i3ty,i3id,i3lo,i3hi]): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1, i2, i3], [i1id, i1lo, i1hi, i2id, i2lo, i2hi, i3id, i3lo, i3hi])
template `[]=`*[D,V;id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4,i1id,i1lo,i1hi,i2id,i2lo,i2hi,i3id,i3lo,i3hi:static[int],i1ty,i2ty,i3ty:static[TPLIndex]](x: gT4[D,V,id1,lo1,hi1,id2,lo2,hi2,id3,lo3,hi3,id4,lo4,hi4], i1: AnyIndex[i1ty,i1id,i1lo,i1hi], i2: AnyIndex[i2ty,i2id,i2lo,i2hi], i3: AnyIndex[i3ty,i3id,i3lo,i3hi], y: V): untyped =
  indexing(x, [id1, lo1, hi1, id2, lo2, hi2, id3, lo3, hi3, id4, lo4, hi4], [i1, i2, i3], [i1id, i1lo, i1hi, i2id, i2lo, i2hi, i3id, i3lo, i3hi], y)

template genUnaryOp(op: untyped): untyped =
  template op*[D,V;id1,lo1,hi1:static[int]](x: gT1[D,V,id1,lo1,hi1]): untyped =
    op(x[automaticIndex(id1,lo1,hi1)])
  template op*[D,V;id1,lo1,hi1,id2,lo2,hi2:static[int]](x: gT2[D,V,id1,lo1,hi1,id2,lo2,hi2]): untyped =
    op(x[automaticIndex(id1,lo1,hi1), automaticIndex(id2,lo2,hi2)])

macro genUOp(os: varargs[untyped]): untyped =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genUnaryOp", o)
genUOp(`+`, `-`)

proc unindexedOp(tmp: NimNode, xrank, yrank: int): NimNode =
  result = tmp.copy
  let
    xd = tmp[2][0][0]
    yd = tmp[2][0][1]
    xv = tmp[2][0][2]
    yv = tmp[2][0][3]
    xid = $tmp[2][1][0]
    xlo = $tmp[2][1][1]
    xhi = $tmp[2][1][2]
    yid = $tmp[2][1][3]
    ylo = $tmp[2][1][4]
    yhi = $tmp[2][1][5]
    x = ident($tmp[3][1][0])
    y = ident($tmp[3][2][0])
  var
    dv = newNimNode(nnkIdentDefs).add(xv, yv)
    id = newNimNode(nnkIdentDefs)
    xtype, ytype: NimNode
    xval, yval: NimNode
  if xrank > 0:
    xtype = newNimNode(nnkBracketExpr).add(ident("gT" & $xrank), xd, xv)
    xval = newNimNode(nnkBracketExpr).add x
    dv.add xd
    for n in 1..xrank:
      id.add(ident(xid & $n), ident(xlo & $n), ident(xhi & $n))
      xtype.add(ident(xid & $n), ident(xlo & $n), ident(xhi & $n))
      xval.add newCall(bindsym"automaticIndex", ident(xid & $n), ident(xlo & $n), ident(xhi & $n))
  else:                         # xrank == 0
    xtype = xv
    xval = x
  if yrank > 0:
    ytype = newNimNode(nnkBracketExpr).add(ident("gT" & $yrank), yd, yv)
    yval = newNimNode(nnkBracketExpr).add y
    dv.add yd
    for n in 1..yrank:
      id.add(ident(yid & $n), ident(ylo & $n), ident(yhi & $n))
      ytype.add(ident(yid & $n), ident(ylo & $n), ident(yhi & $n))
      yval.add newCall(bindsym"automaticIndex", ident(yid & $n), ident(ylo & $n), ident(yhi & $n))
  else:                         # yrank == 0
    ytype = yv
    yval = y
  dv.add(newEmptyNode(), newEmptyNode())
  id.add(tmp[2][1][6], newEmptyNode())
  result[2][0] = dv
  result[2][1] = id
  result[3][1][0] = x
  result[3][1][1] = xtype
  result[3][2][0] = y
  result[3][2][1] = ytype
  result[6][0][1] = xval
  result[6][0][2] = yval
macro genUnIndexedOps(n: static[int]): untyped =
  result = quote do:
    template genBinaryOp(op: untyped): untyped =
      template op*[lD,rD,lV,rV;lid,llo,lhi,rid,rlo,rhi:static[int]](x: xtype, y: ytype): untyped =
        op(x, y)
  result.expectKind nnkStmtList
  result[0].expectKind nnkTemplateDef
  result = result[0]
  #echo result.treerepr
  var tmp = result[6][0]
  tmp.expectKind nnkTemplateDef
  result[6] = newStmtList()
  for lrank in 0..n:
    for rrank in 0..n:
      if lrank == 0 and rrank == 0:
        continue
      result[6].add tmp.unindexedOp(lrank, rrank)
  result = result.copy
  #echo result.repr
  #echo result.treerepr
genUnIndexedOps(maxTensorRanks)
#genUnIndexedOps(2)

#[
template genBinaryOp(op: untyped): stmt =
  template op*[lD,lV,rV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: rV): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1)], y)
  template op*[rD,lV,rV;rid1,rlo1,rhi1:static[int]](x: lV, y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
    op(x, y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,rD,lV,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1)], y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,lV,rV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: rV): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y)
  template op*[rD,lV,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: lV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
    op(x, y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])
  template op*[lD,rD,lV,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y[automaticIndex(rid1,rlo1,rhi1)])
  template op*[lD,rD,lV,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1)], y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])
  template op*[lD,rD,lV,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
    op(x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)], y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)])
]#
macro genBOp(os: varargs[untyped]): untyped =
  result = newStmtList()
  for o in os:
    result.add newCall(bindsym"genBinaryOp", o)
genBOp(`+`, `-`, `*`, `/`, `+=`, `-=`, `*=`, `/=`)

proc convOpToAsgn(n: NimNode): NimNode =
  result = n
  result[6][0] = newAssignment(n[6][0][1], n[6][0][2])
macro genAutoIndexAsgn(n: static[int]): untyped =
  var tmp = quote do:
    template autoIndexAsgn*[lD,rD,lV,rV;lid,llo,lhi,rid,rlo,rhi:static[int]](x: xtype, y: ytype): untyped =
      op(x, y)
  tmp.expectKind nnkStmtList
  tmp[0].expectKind nnkTemplateDef
  tmp = tmp[0]
  result = newStmtList()
  for lrank in 0..n:
    for rrank in 0..n:
      if lrank == 0 and rrank == 0:
        continue
      result.add tmp.unindexedOp(lrank, rrank).convOpToAsgn
  #result = result.copy
  #echo result.repr
  #echo result.treerepr
genAutoIndexAsgn(maxTensorRanks)
#genAutoIndexAsgn(2)
#[
template autoIndexAsgn[lD,lV;lid1,llo1,lhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: lV): untyped =
  x[automaticIndex(lid1,llo1,lhi1)] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1:static[int]](x: rV, y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
  x = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
  x[automaticIndex(lid1,llo1,lhi1)] = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV;lid1,llo1,lhi1,lid2,llo2,lhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: lV): untyped =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y
template autoIndexAsgn[rD,rV;rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: rV, y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
  x = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT1[rD,rV,rid1,rlo1,rhi1]): untyped =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y[automaticIndex(rid1,rlo1,rhi1)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT1[lD,lV,lid1,llo1,lhi1], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
  x[automaticIndex(lid1,llo1,lhi1)] = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
template autoIndexAsgn[lD,lV,rD,rV;lid1,llo1,lhi1,lid2,llo2,lhi2,rid1,rlo1,rhi1,rid2,rlo2,rhi2:static[int]](x: gT2[lD,lV,lid1,llo1,lhi1,lid2,llo2,lhi2], y: gT2[rD,rV,rid1,rlo1,rhi1,rid2,rlo2,rhi2]): untyped =
  x[automaticIndex(lid1,llo1,lhi1),automaticIndex(lid2,llo2,lhi2)] = y[automaticIndex(rid1,rlo1,rhi1),automaticIndex(rid2,rlo2,rhi2)]
]#
macro autoIndexAsgn*[T](lhs: T, rhs: T): untyped =
  dbg "autoIndexAsgn <= lhs: ", lhs, TPLDebug.detail
  dbg "autoIndexAsgn <= rhs: ", rhs, TPLDebug.detail
  var lhs = lhs.unwrap
  if lhs.kind in CallNodes and $lhs[0] == "[]": # Indexing operation
    result = newNimNode(nnkBracketExpr)
    # result = newCall(ident"[]=")
    for i in 1..<lhs.len:
      result.add lhs[i]
  else:
    result = lhs
  result = wrappedAssign(result, rhs)
  dbg "autoIndexAsgn => ", result, TPLDebug.detail
macro autoIndexAsgn*[id,lo,hi:static[int]](lhs: AnyIndex[TPLIndex.index,id,lo,hi], rhs: int): untyped =
  dbg "autoIndexAsgn <= lhs: ", lhs, TPLDebug.detail
  dbg "autoIndexAsgn <= rhs: ", rhs, TPLDebug.detail
  template ixeq(ix: untyped, n: untyped): untyped =
    ix.index = n
  result = getast ixeq(lhs, rhs)
  dbg "autoIndexAsgn => ", result, TPLDebug.detail

macro staticforbody(i: untyped, j: int, t: typed, n: untyped): untyped =
  # echo "\n>>>> staticfor"
  let
    ix = newCall(bindsym"index", t, j)
  result = replace(n, i, ix)
  # echo result.treerepr
  # echo result.repr
  # echo "<<<< staticfor"
template staticforindex*[ty:static[TPLIndex];id,lo,hi:static[int]](i: untyped, t: typedesc[AnyIndex[ty,id,lo,hi]], n: untyped): untyped =
  when hi >= lo:
    unrollfor j, lo, hi:
      staticforbody(i, j, t, n)
  else:
    error "Unsupported statict for index " & i.repr & " of type " & $t & " in " & n.repr
template staticforindex*[ty:static[TPLIndex];id,lo,hi:static[int]](i: untyped, t: AnyIndex[ty,id,lo,hi], n: untyped): untyped =
  staticforindex(i, type(t), n)
macro staticforstmt*(n: typed): untyped =
  # echo "\n>>>> staticforstmt"
  # echo n.treerepr
  expectKind(n, nnkForStmt)
  expectKind(n[1], CallNodes)
  assert "items" == $n[1][0].symbol
  let
    t = n[1][1]
    i = n[0]
    id = gensym(nskForVar, "__" & $i.symbol)
    ii = newCall(bindsym"index", t, id)
    s = convert(n[2], i, ii)
  result = quote do:
    unrollfor `id`, `t`.lo, `t`.hi:
      `s`
  # echo result.treerepr
  # echo "<<<< staticforstmt"
