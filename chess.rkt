#lang forge

option problem_type temporal 
option max_tracelength 10 -- NEEDED! default is 5. need to be able to find the whole lasso.

/*
 * Logic for Systems Final Project - Chess Model
**/

-- We define our board with rows and columns that have previous and next neighbors. There is no actual Board sig, as 
-- we eliminated to improve performance.
abstract sig row {r_prev: lone row, r_next: lone row}
abstract sig col {c_prev: lone col, c_next: lone col}

one sig colA extends col {}
one sig colB extends col {}
one sig colC extends col {}
one sig colD extends col {}
one sig colE extends col {} -- disabled for performance reasons. Reenable to get full 8x8.
// one sig colF extends col {}
// one sig colG extends col {}
// one sig colH extends col {}

one sig row1 extends row {}
one sig row2 extends row {}
one sig row3 extends row {}
one sig row4 extends row {}
one sig row5 extends row {}
// one sig row6 extends row {}
// one sig row7 extends row {}
// one sig row8 extends row {}

-- We have squares that can optionally match to a piece occupying it.
sig square {
  var pc: lone piece,-- square's piece (if any - mutable)
  coord: set row -> col -- square's coordinate (immutable)
}

-- A piece optionally matches to a square that it occupies, plus any squares it can move to. 
abstract sig piece {
  var sq: lone square, -- a piece's square, if it is not captured
  var moves: set square -- all the piece's potentially valid moves (does not account for state restrictions, e.g. king safety)
}

-- These represent our chess pieces, with the letter corresponding to the piece name in chess algebraic notation (excepting pawns). 
sig P extends piece {} -- pawn
sig N extends piece {} -- knight
sig B extends piece {} -- bishop
sig R extends piece {} -- rook
sig Q extends piece {} -- queen
sig K extends piece {} -- king

-- Represents color of pieces 
abstract sig Color {
  pieces: set piece
}

one sig Black extends Color {}
one sig White extends Color {}

-- ======================= COLOR HELPERS =======================

-- enforces color membership - no crossover between teams and all pieces in a team.
pred colorMembership {
  no White.pieces & Black.pieces
  all p : piece | {
    p in (Color.pieces)
  }
}

-- finds if two pieces are the same color
pred isSameColor[p1: piece, p2: piece] {
  (p1 in Black.pieces and p2 in Black.pieces) or 
  (p1 in White.pieces and p2 in White.pieces)
}

-- ======================= SQUARE RELATION HELPERS =======================

-- find adjacent rows or cols
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

-- Find adjacent diagonal squares - 
-- prevcolprevrow = pcpr, nextcolprevrow = ncpr, etc. 
fun pcprDiag[sq: square]: lone square {
  (coord.((sq.coord[row]).c_prev)).(sq.coord.col.r_prev)
}

fun pcnrDiag[sq: square]: lone square {
  (coord.((sq.coord[row]).c_prev)).(sq.coord.col.r_next)
}

fun ncprDiag[sq: square]: lone square {
  (coord.((sq.coord[row]).c_next)).(sq.coord.col.r_prev)
}

fun ncnrDiag[sq: square]: lone square {
  (coord.((sq.coord[row]).c_next)).(sq.coord.col.r_next)
}


-- find full extended diagonals. 
fun pcprDiags[sq: square]: set square {
  pcprDiag[sq] + 
  pcprDiag[pcprDiag[sq]] + 
  pcprDiag[pcprDiag[pcprDiag[sq]]] + 
  pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]// + 
  // pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]] + 
  // pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]]] + 
  // pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[pcprDiag[sq]]]]]]]
}

fun pcnrDiags[sq: square]: set square {
  pcnrDiag[sq] + 
  pcnrDiag[pcnrDiag[sq]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[sq]]] + 
  pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]] //+ 
  // pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]] + 
  // pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]]] + 
  // pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[pcnrDiag[sq]]]]]]]
}

fun ncnrDiags[sq: square]: set square {
  ncnrDiag[sq] + 
  ncnrDiag[ncnrDiag[sq]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[sq]]] + 
  ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]] //+ 
  // ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]] + 
  // ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]]] + 
  // ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[ncnrDiag[sq]]]]]]]
}

fun ncprDiags[sq: square]: set square {
  ncprDiag[sq] + 
  ncprDiag[ncprDiag[sq]] + 
  ncprDiag[ncprDiag[ncprDiag[sq]]] + 
  ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]] //+ 
  // ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]] + 
  // ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]]] + 
  // ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[ncprDiag[sq]]]]]]]
}

-- find all diagonally reachable squares.
fun allDiags[sq: square]: set square {
  pcprDiags[sq] + pcnrDiags[sq] + ncnrDiags[sq] + ncprDiags[sq]
}

-- Tells if two squares are adjacent to each other
pred adjacentTo[s1 : square, s2 : square] {
  s1.coord.col = s2.coord.col implies {
    nextCol[s1] = s2.coord[row] or prevCol[s1] = s2.coord[row]
  }
  s1.coord[row] = s2.coord[row] implies {
    nextRow[s1] = s2.coord.col or prevRow[s1] = s2.coord.col
  }
  (s1.coord.col != s2.coord.col && s1.coord[row] != s2.coord[row]) implies {
    nextRow[s1] = s2.coord.col or prevRow[s1] = s2.coord.col
    nextCol[s1] = s2.coord[row] or prevCol[s1] = s2.coord[row]
  }
}

-- ===================== STRUCTURE + VALIDITY ======================
pred piecesToSquares { -- ensures squares and pieces are one-to-one mapped
  -- bidirectional mapping
  all p: piece | all s: square {
    s in p.sq iff p in s.pc
  }

  -- unique
  all p: piece | {
    lone pc.p
  }
}

-- helper to ensure the squares and coords are one-to-one and onto
pred functionalBoard {
  all s1 : square | {
    no s2 : square - s1 | {
      s1.coord = s2.coord
    }
  }

  all s : square | {
    one s.coord
  }
}

pred structural { -- solely focused on board dimensions
  some row 
  some col

  functionalBoard
  piecesToSquares

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
  // colE.c_next = colF
  // colF.c_next = colG
  // colG.c_next = colH

  row1.r_next = row2
  row2.r_next = row3
  row3.r_next = row4
  row4.r_next = row5
  // row5.r_next = row6
  // row6.r_next = row7
  // row7.r_next = row8
}

-- ================================= Pawn related preds =================================
pred forwardDiagonal[p: P, s : square] {
  some s.pc
  p in White.pieces implies {
    nextRow[pc.p] = s.coord.col
  } else {
    prevRow[pc.p] = s.coord.col
  }
  nextCol[pc.p] = s.coord[row] or prevCol[pc.p] = s.coord[row]
}

pred oneInFront[p : P, s : square] {
  no s.pc
  pc.p.coord[row] = s.coord[row]
  p in White.pieces implies {
    nextRow[pc.p] = s.coord.col
  } else {
    prevRow[pc.p] = s.coord.col
  }
}

pred twoInFront[p : P, s : square] {
  no s.pc
  pc.p.coord[row] = s.coord[row]
  p in White.pieces implies {
    pc.p.coord.col = row2
    nextRow[pc.p].r_next = s.coord.col
  } else {
    // MUST CHANGE FOR LARGER BOARDS -----------------------------------------
    pc.p.coord.col = row4
    prevRow[pc.p].r_prev = s.coord.col
  }
}

pred PMoves[p : P] {
  some pc.p
  all s : square | {
    s in p.moves iff {
      some s.pc implies not isSameColor[p, s.pc]
      oneInFront[p, s] or twoInFront[p, s] or forwardDiagonal[p, s]
    }
  }
}

-- ================================= King related preds =================================
pred validKings { -- should only and always have 2 kings.
  #(K) = 2
  all k: K | {
    some pc.k
  }
  one k: K | {
    k in White.pieces
  }
  one k: K | {
    k in Black.pieces
  }
}

pred kingSafety {
  no p : piece | {
    (pc.K) in p.moves 
  }
}

pred inCheck[k : K]{
  some p : piece | {
      pc.k in p.moves
      not isSameColor[k, p]
    }
}

pred twoChecks[k : K] {
  inCheck[k]
  after inCheck[k]
}

pred adjacentKings {
  some k1 : K | {
    some k2 : K - k1 {
      adjacentTo[pc.k1, pc.k2]
    }
  }
}

pred KMoves[k : K] {
  some pc.k
  all s : square | {
    s in k.moves iff {
      adjacentTo[pc.k, s]
      some s.pc implies not isSameColor[k, s.pc]
      no p : piece | {
        s in p.moves
        not isSameColor[k, p]
      }
      no k2 : K - k | {
        adjacentTo[pc.k2, s]
      }
    }
  }
}

-- ================================= Bishop related preds =================================
pred BMoves[b: B] { -- enforces valid moves
  all s: square | { -- For all squares, ...
    s in b.moves iff { -- square is in bishop's legal moves iff ...
      some s.pc implies not isSameColor[b, s.pc]
      validMovesForBishop[s, b]
    }
  }
}

-- collects the set of valid moves
pred validMovesForBishop[a: square, b: piece] {  -- should be B, but piece to allow reuse with Queen 
  -- true for square a if it is on a diagonal square that is not blocked
    (a in pcprDiags[pc.b] and (no p: piece | {some pc.p and pc.p in pcprDiags[pc.b] and pc.p in ncnrDiags[a]})) or
    (a in pcnrDiags[pc.b] and (no p: piece | {some pc.p and pc.p in pcnrDiags[pc.b] and pc.p in ncprDiags[a]})) or
    (a in ncprDiags[pc.b] and (no p: piece | {some pc.p and pc.p in ncprDiags[pc.b] and pc.p in pcnrDiags[a]})) or
    (a in ncnrDiags[pc.b] and (no p: piece | {some pc.p and pc.p in ncnrDiags[pc.b] and pc.p in pcprDiags[a]}))
}

-- ================================= Knight related preds =================================
pred NMoves[n: N] {
  all s: square | {
    s in n.moves iff {
      some s.pc implies not isSameColor[n, s.pc]
      validMovesForKnight[s, n]
    }
  }
}

pred validMovesForKnight[a: square, n: N] {
  { pc.n.coord.col = a.coord.col.r_next and pc.n.coord[row] = (a.coord[row]).c_next.c_next } or 
  { pc.n.coord.col = a.coord.col.r_next and pc.n.coord[row] = (a.coord[row]).c_prev.c_prev } or 
  { pc.n.coord.col = a.coord.col.r_prev and pc.n.coord[row] = (a.coord[row]).c_next.c_next } or 
  { pc.n.coord.col = a.coord.col.r_prev and pc.n.coord[row] = (a.coord[row]).c_prev.c_prev } or 
  { pc.n.coord[row] = (a.coord[row]).c_next and pc.n.coord.col = a.coord.col.r_next.r_next } or 
  { pc.n.coord[row] = (a.coord[row]).c_next and pc.n.coord.col = a.coord.col.r_prev.r_prev } or 
  { pc.n.coord[row] = (a.coord[row]).c_prev and pc.n.coord.col = a.coord.col.r_next.r_next } or 
  { pc.n.coord[row] = (a.coord[row]).c_prev and pc.n.coord.col = a.coord.col.r_prev.r_prev }
}

-- ================================= Rook related preds =================================
pred RMoves[r: R] {
  all s: square | {
    s in r.moves iff {
      some s.pc implies not isSameColor[r, s.pc]
      validMovesForRook[s, r]
    }
  }
}
 
pred validMovesForRook[a: square, r: piece] { 
  -- exclude its own square
  not pc.r = a

  -- the after piece is in the same row or col
  pc.r.coord.col = a.coord.col or pc.r.coord[row] = a.coord[row]

  -- no other pieces in the space between the before and after squares
  -- if same row (moved cols)
  pc.r.coord.col = a.coord.col => {
      -- if moving down cols 
    pc.r.coord[row] in (a.coord[row]).^c_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord[row] in ((a.coord[row]).^c_next & (pc.r.coord[row]).^c_prev) and (pc.r.coord.col = s.coord.col) => {
        no s.pc
      } 
    } 
    -- if moving up the cols 
    a.coord[row] in (pc.r.coord[row]).^c_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord[row] in ((a.coord[row]).^c_prev & (pc.r.coord[row]).^c_next) and (pc.r.coord.col = s.coord.col) => {
        no s.pc
      } 
    }
  } 
  -- if same col (moved rows)
  pc.r.coord[row] = a.coord[row] => {
      -- if moving down rows 
    pc.r.coord.col in a.coord.col.^r_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord.col in ((a.coord.col.^r_next) & (pc.r.coord.col.^r_prev)) and (pc.r.coord[row] = s.coord[row]) => {
        no s.pc
      }
    } 
    -- if moving up the rows 
    a.coord.col in pc.r.coord.col.^r_next => {
      -- set of intermediate pieces is empty 
      all s : square | s.coord.col in ((a.coord.col.^r_prev) & (pc.r.coord.col.^r_next)) and (pc.r.coord[row] = s.coord[row]) => {
        no s.pc
      }
    }
  }
}

-- ================================= Queen related preds =================================

pred QMoves[q: Q] { -- just rook + bishop
  all s: square | {
    s in q.moves iff {
      some s.pc implies not isSameColor[q, s.pc]
      validMovesForRook[s, q] or validMovesForBishop[s, q]
    }
  }
}

--- ================================= General move-related preds =================================

-- makes any move for any piece.
pred generalMove[p : piece] {
  some s : square | {
    s in p.moves
    some s.pc implies {
      pc' = pc - (pc.p -> p) - (s -> s.pc) + (s -> p)
    } else {
      pc' = pc - (pc.p -> p) + (s -> p) 
    }
  }
  --  Prevents king from being attacked after move.
  after { no k: K | { isSameColor[k, p] and inCheck[k] }}
}


-- ensures all pieces maintain valid moves 
pred allMoves {
  all p: P | some pc.p implies {PMoves[p]} else {no p.moves}
  all b: B | some pc.b implies {BMoves[b]} else {no b.moves}
  all n: N | some pc.n implies {NMoves[n]} else {no n.moves}
  all r: R | some pc.r implies {RMoves[r]} else {no r.moves}
  all q: Q | some pc.q implies {QMoves[q]} else {no q.moves}
  all k: K | some pc.k implies {KMoves[k]} else {no k.moves}
}

-- checks if a state is checkmate
pred checkmate {
  some k : K | {
    -- A state where the king is under attack
    some p1 : piece {
      not isSameColor[k, p1] -- piece is not same color
      pc.k in p1.moves -- king under attack
      no p3 : piece | { -- no piece that can move and end the threat
        isSameColor[k, p3] 
        generalMove[p3] 
      }
    }
    no k.moves -- king can't move
  }
}

-- ================================= State restrictions =================================

-- white's move
pred whiteMove {
  some p: White.pieces | { generalMove[p] } 
}

-- black's move
pred blackMove {
  some p: Black.pieces | { generalMove[p] }
}

-- turns
pred turns {
  whiteMove implies { after (blackMove and not whiteMove)}
  blackMove implies { after (whiteMove and not blackMove)}
}

-- init state for move sequences
pred init {
  not checkmate
  whiteMove
  not adjacentKings
  colorMembership
  all p: piece | {
    some p.sq
  }
}

-- traces for move sequences
pred traces {
  init
  always {
    colorMembership
    structural
    allMoves
    turns
  }
}


-- checkmate related state stuff
pred init2 {
  whiteMove or blackMove
  all p: piece | {
    some p.sq
  }
}

-- can't be white's move if black is in check and vice versa
pred checkAndNotMove {
  whiteMove implies {
    no k: K | { k in Black.pieces and inCheck[k] }
  }
  blackMove implies {
    no k: K | { k in White.pieces and inCheck[k] }
  }
}

-- traces, but for checkmate in 1
pred mate1 {
  init2
  validKings
  always {
    colorMembership
    structural
    allMoves
    checkAndNotMove
  }
  after checkmate 
}


pred static {
  colorMembership
  structural
  allMoves
}

-- =================== generating move sequences =========================

-- indicates what pieces are in example. Uncomment desired pieces and change # of pieces in run accordingly.
pred scenario {

  // #(Black.pieces & K) = 1
  // #(White.pieces & K) = 1

  // #(Black.pieces & Q) = 1
  // #(White.pieces & Q) = 1
  // #(Black.pieces & R) = 1
  // #(White.pieces & R) = 1
  // #(Black.pieces & B) = 1
  // #(White.pieces & B) = 1
  // #(Black.pieces & N) = 1
  // #(White.pieces & N) = 1
  // #(Black.pieces & P) = 1
  // #(White.pieces & P) = 1
}

-- this is a sequence of endgame moves in a position with 3 pieces.
// run {traces and scenario} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 2 K, exactly 1 R

-- ==================== generating mate in 1 examples =======================================

-- various common endgame scenarios where mate in 1 may or may not be possible. 

// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 N, exactly 2 K -- unsat because 1 N checkmate impossible.
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 N, exactly 2 K -- sat because 2 N checkmate poss.
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 B, exactly 2 K -- unsat because 1 B checkmate impossible.
run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 B, exactly 2 K -- sat because 2 B checkmate poss.
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 1 B, exactly 1 N, exactly 2 K -- sat
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 R, exactly 2 K -- sat 
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 R, exactly 2 K -- sat
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 Q, exactly 2 K -- sat
// run {mate1} for exactly 8 col, exactly 8 row, exactly 64 square, exactly 4 piece, exactly 2 R, exactly 2 K -- sat -- stress test. 
-- REMEMBER TO UNCOMMENT ROW/COL/DIAG as well!
// run {mate 1  and #(Black.pieces) = 3} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 R, exactly 2 K -- sat

// pred demo {
//   #(B + N) = 2 or
//   (#(R + Q) = 2 and #(pieces.R + pieces.Q) = 1)
// }

// run {mate1 and demo} for exactly 5 col, exactly 5 row, exactly 25 square, 4 piece, exactly 2 K -- for demoing random assortment of checkmates
-- not useful because still only generates rooks, + visualizer breaks