#lang forge

option problem_type temporal 
option max_tracelength 10 -- NEEDED! default is 5. need to be able to find the whole lasso.

/*
 * Logic for Systems Final Project - Chess Model
**/

-- We define our board with rows and columns that have previous and next neighbors.
sig row {r_prev: lone row, r_next: lone row}
sig col {c_prev: lone col, c_next: lone col}

-- We have squares that can optionally match to a piece occupying it.
sig square {var pc: lone piece}

-- A piece optionally matches to a square that it occupies, plus any squares it can move to. 
abstract sig piece {
  var sq: lone square,
  var moves: set square
}

-- These represent our chess pieces, with the letter corresponding to the piece name in algebraic notation (excepting pawns). 
sig P extends piece {} -- pawn
sig N extends piece {} -- knight
sig B extends piece {} -- bishop
sig R extends piece {} -- rook
sig Q extends piece {} -- queen
sig K extends piece {} -- king

-- The board contains places that are rows to cols to squares. 
one sig Board {
  -- Each row, col pair maps to a cell
  places: set row -> col -> square
}

pred structural { -- solely focused on board dimensions
  some row 
  some col

  -- single square occupancy
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
  -- king is on some square
  -- can go to all adjacent squares. i.e. nextrow, row, prevrow x nextcol, col, prevcol
  -- ^ above method doesn't seem to extend to longer range pieces e.g. queen
}

-- to check for blocking pieces, get row/col/whatever. then, for the blocking piece, get the difference of its line of sight
-- to the piece. ex:
-- a . . . x . . . a's horizontal moves can be found by a.next^ - x.next*

-- Diagonals TODO
-- (r_next.( row -> col ).c_next)^  ?
-- function that returns a diagonal
-- hard code diagonals into squares

pred moveK

pred generatePuzzle {
  structural
}

run {generatePuzzle} for exactly 8 col, exactly 8 row, exactly 64 square, exactly 1 piece, exactly 1 K