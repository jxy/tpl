type
  seqset*[T] = object
    s: seq[T]
proc len*(s: seqset): auto = s.s.len
iterator items*[T](s: seqset[T]): T =
  for i in s.s:
    yield i
iterator pairs*[T](s: seqset[T]): (int, T) =
  for i, j in s.s:
    yield (i, j)
proc copy*[T](s: seqset[T]): seqset[T] =
  result.s.newseq 0
  for x in s:
    result.s.add x
proc contains*[T](s: seqset[T], x: T): bool =
  for i in s:
    if x == i:
      return true
  return false
proc contains*[T](s, xs: seqset[T]): bool =
  for x in xs:
    if x notin s:
      return false
  return true
proc init*[T](s: var seqset[T]) = newseq(s.s,0)
proc incl*[T](s: var seqset[T], x: T) =
  if x notin s:
    s.s.add x
proc incl*[T](s: var seqset[T], x: seqset[T]) =
  for i in x:
    s.incl i
proc `+`*[T](x: seqset[T], y: seqset[T]): seqset[T] =
  result = x.copy
  result.incl y
proc `+=`*[T](x: var seqset[T], y: seqset[T]) =
  x.incl y
proc excl*[T](s: var seqset[T], x: T) =
  for n, i in s.s:
    if x == i:
      s.s.delete n
      break
proc excl*[T](s: var seqset[T], x: seqset[T]) =
  for i in x:
    s.excl i
proc `-`*[T](x: seqset[T], y: seqset[T]): seqset[T] =
  result = x.copy
  result.excl y
proc intersection*[T](x: seqset[T], y:seqset[T]): seqset[T] =
  result.init
  for i in x:
    if i in y:
      result.incl i
