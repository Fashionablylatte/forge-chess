#lang forge

option problem_type temporal 
option max_tracelength 3 -- NEEDED! default is 5. need to be able to find the whole lasso.
// option solver MiniSatProver
// option logtranslation 1
// option coregranularity 1
// option core_minimization rce

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
// one sig colE extends col {} -- disabled for performance reasons
// one sig colF extends col {}
// one sig colG extends col {}
// one sig colH extends col {}

one sig row1 extends row {}
one sig row2 extends row {}
one sig row3 extends row {}
one sig row4 extends row {}
// one sig row5 extends row {}
// one sig row6 extends row {}
// one sig row7 extends row {}
// one sig row8 extends row {}

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
abstract sig P extends piece {} -- pawn
abstract sig N extends piece {} -- knight
abstract sig B extends piece {} -- bishop
abstract sig R extends piece {} -- rook
abstract sig Q extends piece {} -- queen
abstract sig K extends piece {} -- king

sig WP extends P {} -- white pawn
sig WN extends N {} -- white knight
sig WB extends B {} -- white bishop
sig WR extends R {} -- white rook
sig WQ extends Q {} -- white queen
sig WK extends K {} -- white king

sig BP extends P {} -- black pawn
sig BN extends N {} -- black knight
sig BB extends B {} -- black bishop
sig BR extends R {} -- black rook
sig BQ extends Q {} -- black queen
sig BK extends K {} -- black king

-- The board contains places that are rows to cols to squares. 
one sig Board {
  -- Each row, col pair maps to a cell
  places: set row -> col -> square
}

-- Represents color of pieces 
abstract sig Color {
  pieces: set piece
}

one sig Black extends Color {}
one sig White extends Color {}

-- preds for color membership
pred colorMembership {
  all p: piece | {
    // p in (WP + WN + WB + WR + WQ + WK) iff p in White.pieces
    // p in (BP + BN + BB + BR + BQ + BK) iff p in Black.pieces
  }
}

-- finds if two pieces are the same color
pred isSameColor[p1: piece, p2: piece] {
  (p1 in Black.pieces and p2 in Black.pieces) or 
  (p1 in White.pieces and p2 in White.pieces)
}

-- Helpers for finding square relations
fun prevRow[sq: square]: lone row {
  sq.coord.col.r_prev
}

fun nextRow[sq: square]: lone row {
  sq.coord.col.r_next
}

fun prevCol[sq: square]: lone col {
  (sq.coord[row]).c_prev
}

fun nextCol[sq: square]: lone col {
  (sq.coord[row]).c_next
}

fun pcprDiag[sq: square]: lone square {
  (prevCol[sq]).((prevRow[sq]).(Board.places)) 
}

fun pcnrDiag[sq: square]: lone square {
  (prevCol[sq]).((nextRow[sq]).(Board.places)) 
}

fun ncprDiag[sq: square]: lone square {
  (nextCol[sq]).((prevRow[sq]).(Board.places)) 
}

fun ncnrDiag[sq: square]: lone square {
  (nextCol[sq]).((nextRow[sq]).(Board.places)) 
}

fun pcprDiags[sq: square]: set square {
  pcprDiag[sq] + 
  pcprDiag[pcprDiag[sq]] + 
  pcprDiag[pcprDiag[pcprDiag[sq]]] + 
  pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]] + 
  pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]] + 
  pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]]] + 
  pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]]]]
}

fun pcnrDiags[sq: square]: set square {
  pcnrDiag[sq] + 
  pcnrDiag[pcnrDiag[sq]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[sq]]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]]]]
}

fun ncnrDiags[sq: square]: set square {
  ncnrDiag[sq] + 
  ncnrDiag[ncnrDiag[sq]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[sq]]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]]]]
}

fun ncprDiags[sq: square]: set square {
  ncprDiag[sq] + 
  ncprDiag[ncprDiag[sq]] + 
  ncprDiag[ncprDiag[ncprDiag[sq]]] + 
  ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]] + 
  ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]] + 
  ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]]] + 
  ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]]]]
}

fun allDiags[sq: square]: set square {
  pcprDiags[sq] + pcnrDiags[sq] + ncnrDiags[sq] + ncprDiags[sq]
}

-- STRUCTURE + VALIDITY ----------------------
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
  // colD.c_next = colE
  // colE.c_next = colF
  // colF.c_next = colG
  // colG.c_next = colH

  row1.r_next = row2
  row2.r_next = row3
  row3.r_next = row4
  // row4.r_next = row5
  // row5.r_next = row6
  // row6.r_next = row7
  // row7.r_next = row8

  -- maps each square to its coords
  all sq: square | all r: row | all c: col | {
      r->c->sq in Board.places implies { r->c = sq.coord } 
  }

  -- diagonal relations were too computationally expensive to generate in advance.
}

pred piecesToSquares { -- ensures squares and pieces are one-to-one mapped
  -- bidirectional mapping
  all p: piece | all s: square {
    s in p.sq implies p in s.pc
  }

  -- unique
  all p: piece | {
    lone pc.p
  }
}

-- King related preds --------------------------
pred validKings { -- should only and always have 2 kings.
  #(K) = 2
  all k: K | {
    some k.sq
    some pc.k
  }
}

pred KMoves[k : K] {

  -- King must be on the board currently
  some k.sq
    -- There is some square that the king can move to
  all s : square | {
    -- The square must be adjacent to the square of the king
    -- Does not yet count for squares that are protected by an opposing piece
    s in k.moves iff {
      adjacentTo[k.sq, s]
    }
  }
}

-- Imagine that s1 is the square that remains stationary, and we check if s2 is in any of the 8 squares surrounding s1
pred adjacentTo[s1 : square, s2 : square] {
  -- If the row coordinates are the same, the col coordinate must either be the next or prev
  s1.coord.col = s2.coord.col implies {
    nextCol[s1] = s2.coord[row] or prevCol[s1] = s2.coord[row]
  }

  -- If the col coordinates are the same, the row coordinate must either be the next or prev
  s1.coord[row] = s2.coord[row] implies {
    nextRow[s1] = s2.coord.col or prevRow[s1] = s2.coord.col
  }

  -- If neither the row or col coordinates are the same, then the row coord must be either the next or prev, and the col coord must also be either the next or prev
  (s1.coord.col != s2.coord.col && s1.coord[row] != s2.coord[row]) implies {
    nextRow[s1] = s2.coord.col or prevRow[s1] = s2.coord.col
    nextCol[s1] = s2.coord[row] or prevCol[s1] = s2.coord[row]
  }
}

-- Bishop related preds --------------------------
pred BMoves[b: B] {
  -- need to add legality for king safety. If king in danger, none, else, ...?
  all s: square | { -- For all squares, ...
    s in b.moves iff { -- square is in bishop's legal moves iff ...
      validMovesForBishop[s, b]
    }
  }
}

pred validMovesForBishop[a: square, b: piece] {  -- should be B, but piece to allow reuse with Queen 
  -- true for square a if it is on a diagonal square that is not blocked
    (a in pcprDiags[b.sq] and (no p: piece | {p.sq in pcprDiags[b.sq] and p.sq in ncnrDiags[a]})) or
    (a in pcnrDiags[b.sq] and (no p: piece | {p.sq in pcnrDiags[b.sq] and p.sq in ncprDiags[a]})) or
    (a in ncprDiags[b.sq] and (no p: piece | {p.sq in ncprDiags[b.sq] and p.sq in pcnrDiags[a]})) or
    (a in ncnrDiags[b.sq] and (no p: piece | {p.sq in ncnrDiags[b.sq] and p.sq in pcprDiags[a]}))
}

-- Knight related preds ------------------------------
pred NMoves[n: N] {
  all s: square | {
    s in n.moves iff {
      validMovesForKnight[s, n]
    }
  }
}
pred validMovesForKnight[a: square, n: N] {
  { n.sq.coord.col = a.coord.col.r_next and n.sq.coord[row] = (a.coord[row]).c_next.c_next } or 
  { n.sq.coord.col = a.coord.col.r_next and n.sq.coord[row] = (a.coord[row]).c_prev.c_prev } or 
  { n.sq.coord.col = a.coord.col.r_prev and n.sq.coord[row] = (a.coord[row]).c_next.c_next } or 
  { n.sq.coord.col = a.coord.col.r_prev and n.sq.coord[row] = (a.coord[row]).c_prev.c_prev } or 
  { n.sq.coord[row] = (a.coord[row]).c_next and n.sq.coord.col = a.coord.col.r_next.r_next } or 
  { n.sq.coord[row] = (a.coord[row]).c_next and n.sq.coord.col = a.coord.col.r_prev.r_prev } or 
  { n.sq.coord[row] = (a.coord[row]).c_prev and n.sq.coord.col = a.coord.col.r_next.r_next } or 
  { n.sq.coord[row] = (a.coord[row]).c_prev and n.sq.coord.col = a.coord.col.r_prev.r_prev }
}

-- Rook related preds --------------------------
pred RMoves[r: R] {
  all s: square | {
    s in r.moves iff {
      validMovesForRook[s, r]
    }
  }
}
 
pred validMovesForRook[a: square, r: piece] { -- TODO does not exclude its own starting square
  -- assuming that: 
  -- rook starts on some square, some square has it
  -- ends on some square, some square' has it
  -- captures happen if other color piece in r's square' (aka square') doesn't
  --    have piece of same color
  -- squares for which this predicate is false won't be in r.moves

  -- exclude its own square TODO double check
  not r.sq = a

  -- the after piece is in the same row or col
  r.sq.coord.col = a.coord.col or r.sq.coord[row] = a.coord[row]

  -- no other pieces in the space between the before and after squares
  -- if same row (moved cols)
  r.sq.coord.col = a.coord.col => {
      -- if moving down cols 
    r.sq.coord[row] in (a.coord[row]).^c_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord[row] in ((a.coord[row]).^c_next & (r.sq.coord[row]).^c_prev) and (r.sq.coord.col = s.coord.col) => {
        no s.pc
      } 
    } 
    -- if moving up the cols 
    a.coord[row] in (r.sq.coord[row]).^c_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord[row] in ((a.coord[row]).^c_prev & (r.sq.coord[row]).^c_next) and (r.sq.coord.col = s.coord.col) => {
        no s.pc
      } 
    }
  } 
  -- if same col (moved rows)
  r.sq.coord[row] = a.coord[row] => {
      -- if moving down rows 
    r.sq.coord.col in a.coord.col.^r_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord.col in ((a.coord.col.^r_next) & (r.sq.coord.col.^r_prev)) and (r.sq.coord[row] = s.coord[row]) => {
        no s.pc
      }
    } 
    -- if moving up the rows 
    a.coord.col in r.sq.coord.col.^r_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord.col in ((a.coord.col.^r_prev) & (r.sq.coord.col.^r_next)) and (r.sq.coord[row] = s.coord[row]) => {
        no s.pc
      }
    }
  }
}

-- Queen related preds -------------------------

pred QMoves[q: Q] {
  all s: square | {
    s in q.moves iff {
      validMovesForRook[s, q] or validMovesForBishop[s, q]
    }
  }
}

--- General move-related preds --------------

-- also need to consider: white cannot move unless black moves b4, vice versa
-- KNOWN BUGS: 
pred generalMove[p : piece] {
  -- some square before 
  some p.sq
  -- some square after 
  some p.sq' 
  -- valid move 
  p.sq' in p.moves
  -- captured 
  some s : square | (s = p.sq' and some s.pc) and (not isSameColor[s.pc, p]) => {
    s.pc not in square.pc'
    square.pc - s.pc = square.pc'
  } else {
    square.pc = square.pc'
  }
  all other : piece - p | not other.sq = p.sq' => {
    other.sq' = other.sq
  }
  all other : piece - p | other.sq = p.sq' => {
    other.sq' = other.sq or no other.sq'
  }
}

-- ensures all pieces maintain valid moves 
pred allMoves {
  all b: B | { BMoves[b] }
  all n: N | { NMoves[n] }
  all r: R | { RMoves[r] }
  all q: Q | { QMoves[q] }
  all k: K | { KMoves[k] }
}

pred validBoard { -- position legality 
  // validKings
  piecesToSquares
  colorMembership
}

-- init state  
pred init {
  some p: piece | {
    some p.sq
  }
}

-- traces 
pred traces {
  always { validBoard }
  always { one p: piece | generalMove[p] } 
}

-- generates a chess puzzle 
pred generatePuzzle {
  init
  always {
    structural
    allMoves }
  traces
  // always { validBoard }
  // always { allMoves }
  // B.sq.coord = row2->colB
  // N.sq.coord = row3->colB
  // R.sq.coord = row4->colB
  // Q.sq.coord = row4->colA
  // K.sq.coord = row2->colC
}

-- generates a 5x5 board 
run {generatePuzzle} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 5 piece, exactly 1 BB, exactly 1 WN, exactly 1 WR, exactly 1 BQ, exactly 1 BK
