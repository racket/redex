#lang rhombus
// this file depends on rhombus but there
// is no dependency at the package level
// on rhombus currently; eventually we'll
// want to get rid of the explicit dependency
// on rhombus by replacing this file with
// racket code that does the same thing

import: pict open
export: find from_handle

fun find(pict,sub,h,v):
  Find(sub, ~horiz: h, ~vert: v).in(pict)

fun from_handle(p):
  Pict.from_handle(p)
