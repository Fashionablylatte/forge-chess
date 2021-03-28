#lang forge

option problem_type temporal 
option max_tracelength 10 -- NEEDED! default is 5. need to be able to find the whole lasso.

sig row {r_prev: lone row, r_next: lone row}

-- 
sig col {c_prev: lone col, c_next: lone col}

abstract sig piece {
  var sq: lone square,
  var moves: set square -- ?
}

sig square {var pc: lone piece}

-- These represent the numbers 0-8, which are the only possible numbers in our grid
sig P extends piece {}
sig N extends piece {}
sig B extends piece {}
sig R extends piece {}
sig Q extends piece {}
sig K extends piece {}

one sig Board {
  -- Each row, col pair maps to a cell
  places: set row -> col -> square
}

pred structural { -- solely focused on board dimensions
  -- Either a mine or a number is in each cell
  some row 
  some col
  all b: Board | all i: row | all j: col | lone b.places[i][j]
  all s: square | all b: Board | one (b.places).s
  -- one row that doesn't have prev, one doesn't have next
  one r: row | {no r.r_next}
  one r: row | {no r.r_prev}
  -- all rows reachable from other rows via ^next or ^prev
  all r: row | {r.(*r_next + *r_prev) = row and (*r_next  + *r_prev).r = row} 
  -- bidirectional - this.next's prev = this
  all r1: row | all r2: row | {r1.r_next = r2 implies r2.r_prev = r1}

  -- same but for cols
  -- one col that doesn't have prev, one doesn't have next
  one c: col | {no c.c_next}
  one c: col | {no c.c_prev}
  -- all cols reachable from other cols via ^next or ^prev
  all c: col | {c.(*c_next + *c_prev) = col and (*c_next  + *c_prev).c = col} 
  -- bidirectional - this.next's prev = this
  all c1: col | all c2: col | {c1.c_next = c2 implies c2.c_prev = c1}
}

pred validBoard { -- position legality 

}

pred KMoves[k: King]{
  some k.sq
  k.moves = -- TODO
  -- places = Board->row->col->sq
  -- row = (((Board.places.(k.sq))).col
  -- col = row.(((Board.places.(k.sq)))
}

pred moveK

pred generatePuzzle {
  structural
}

run {generatePuzzle} for exactly 8 col, exactly 8 row, exactly 64 square, exactly 1 piece, exactly 1 K