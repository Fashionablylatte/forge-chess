#lang forge

option problem_type temporal 
option max_tracelength 10 -- NEEDED! default is 5. need to be able to find the whole lasso.

/*
 * Logic for Systems Final Project - Chess Model
**/

-- We define our board with rows and columns that have previous and next neighbors.
abstract sig row {r_prev: lone row, r_next: lone row}
abstract sig col {c_prev: lone col, c_next: lone col}

one sig colA extends col {}
one sig colB extends col {}
one sig colC extends col {}
one sig colD extends col {}
one sig colE extends col {}
one sig colF extends col {}
one sig colG extends col {}
one sig colH extends col {}

one sig row1 extends row {}
one sig row2 extends row {}
one sig row3 extends row {}
one sig row4 extends row {}
one sig row5 extends row {}
one sig row6 extends row {}
one sig row7 extends row {}
one sig row8 extends row {}

-- We have squares that can optionally match to a piece occupying it.
sig square {
  var pc: lone piece,
  coord: set row -> col
  }

-- A piece optionally matches to a square that it occupies, plus any squares it can move to. 
abstract sig piece {
  var sq: lone square,
  var moves: set square -- TODO how to make this single?
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

  -- enforces 8x8 coordinates.
  colA.c_next = colB
  colB.c_next = colC
  colC.c_next = colD
  colD.c_next = colE
  colE.c_next = colF
  colF.c_next = colG
  colG.c_next = colH

  row1.r_next = row2
  row2.r_next = row3
  row3.r_next = row4
  row4.r_next = row5
  row5.r_next = row6
  row6.r_next = row7
  row7.r_next = row8

  -- maps each square to its coords
  all sq: square | all r: row | all c: col | {
      r->c->sq in Board.places implies { r->c = sq.coord } 
    }
}

pred piecesToSquares {
  -- bidirectional mapping
  all p: piece | all s: square {
    s in p.sq implies p in s.pc
  }

  -- unique
  all p: piece | {
    lone pc.p
  }
}

pred validKings {
  #(K) = 2
  all k: K | {
    some k.sq
    some pc.k
  }
}

pred validBoard { -- position legality 
  validKings
  piecesToSquares
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

pred moveK {

}

pred init {
  all p: piece | {
    some p.sq
  }
}

pred generatePuzzle {
  structural
  init
  always { validBoard }
}

fun topDiag[sq: square]: lone square {
  { square } -- TODO
}

run {generatePuzzle and validBoard} for exactly 8 col, exactly 8 row, exactly 64 square, exactly 5 piece, exactly 2 K, exactly 1 B, exactly 1 Q, exactly 1 N