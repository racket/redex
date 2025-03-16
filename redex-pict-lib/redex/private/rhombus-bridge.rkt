#lang rhombus
// this file depends on rhombus but there
// is no dependency at the package level
// on rhombus currently; eventually we'll
// want to get rid of the explicit dependency
// on rhombus by replacing this file with
// racket code that does the same thing

import: pict open
export: is_pict

fun is_pict(pict): pict is_a Pict
