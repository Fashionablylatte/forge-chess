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
  whiteMove
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

------------------ TESTING + VERIFICATION --------------------

--- SUPER BASIC TESTS --- 
test expect {
  -- vacuity check (some traces for an 5x5 board)
  vacuityTest :  { traces } for exactly 5 col, exactly 5 row is sat 
}

------------------ FORMAL STRUCTURAL TESTS --------------------
-- basic instance: an empty board 
inst emptyBoard {
  -- rows and cols
  colA = colA0
  colB = colB0
  colC = colC0
  colD = colD0
  colE = colE0

  row1 = row10
  row2 = row20
  row3 = row30
  row4 = row40
  row5 = row50

  row = row10 + row20 + row30 + row40 + row50
  col = colA0 + colB0 + colC0 + colD0 + colE0

  c_prev = colB0->colA0 + colC0->colB0 + colD0->colC0 + colE0->colD0
  c_next = colA0->colB0 + colB0->colC0 + colC0->colD0 + colD0->colE0
  r_prev = row20->row10 + row30->row20 + row40->row30 + row50->row40
  r_next = row10->row20 + row20->row30 + row30->row40 + row40->row50

  -- squares 
  square = square0 + square1 + square2 + square3 + square4 + square5 + 
    square6 + square7 + square8 + square9 + square10 + square11 + 
    square12 + square13 + square14 + square15 + square16 + square17 + 
    square18 + square19 + square20 + square21 + square22 + square23 + 
    square24
  
  coord = square0->row1->colA + square1->row1->colB + square2->row1->colC + square3->row1->colD + 
    square4->row1->colE + square5->row2->colA + square6->row2->colB + square7->row2->colC + 
    square8->row2->colD + square9->row2->colE + square10->row3->colA + square11->row3->colB + 
    square12->row3->colC + square13->row3->colD + square14->row3->colE + square15->row4->colA + 
    square16->row4->colB + square17->row4->colC + square18->row4->colD + square19->row4->colE + 
    square20->row5->colA + square21->row5->colB + square22->row5->colC + square23->row5->colD + 
    square24->row5->colE

  -- chess pieces
  P = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9
  N = N0 + N1 + N2 + N3
  B = B0 + B1 + B2 + B3
  R = R0 + R1 + R2 + R3
  Q = Q0 + Q1
  K = K0 + K1

  piece = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + N0 + N1 + N2 + N3 + 
    B0 + B1 + B2 + B3 + R0 + R1 + R2 + R3 + Q0 + Q1 + K0 + K1

  -- color 
  Black = Black0 
  White = White0
  Color = Black0 + White0
  
  pieces = Black0->P0 + Black0->P1 + Black0->P2 + Black0->P3 + Black0->P4 + White0->P5 + 
    White0->P6 + White0->P7 + White0->P8 + White0->P9 + Black0->N0 + Black0->N1 + 
    White0->N2 + White0->N3 + Black0->B0 + Black0->B1 + White0->B2 + White0->B3 + 
    Black0->R0 + Black0->R1 + White0->R2 + White0->R3 + Black0->Q0 + White0->Q1 + 
    Black0->K0 + White0->K1
}

-- board with 2+ squares mapping to same coordinates 
inst doubleMapBoard {
    -- rows and cols
  colA = colA0
  colB = colB0
  colC = colC0
  colD = colD0
  colE = colE0

  row1 = row10
  row2 = row20
  row3 = row30
  row4 = row40
  row5 = row50

  row = row10 + row20 + row30 + row40 + row50
  col = colA0 + colB0 + colC0 + colD0 + colE0

  c_prev = colB0->colA0 + colC0->colB0 + colD0->colC0 + colE0->colD0
  c_next = colA0->colB0 + colB0->colC0 + colC0->colD0 + colD0->colE0
  r_prev = row20->row10 + row30->row20 + row40->row30 + row50->row40
  r_next = row10->row20 + row20->row30 + row30->row40 + row40->row50

  -- squares 
  square = square0 + square1 + square2 + square3 + square4 + square5 + 
    square6 + square7 + square8 + square9 + square10 + square11 + 
    square12 + square13 + square14 + square15 + square16 + square17 + 
    square18 + square19 + square20 + square21 + square22 + square23 + 
    square24
  
  -- two squares map to 2D
  coord = square0->row1->colA + square1->row1->colB + square2->row1->colC + square3->row1->colD + 
    square4->row1->colE + square5->row2->colA + square6->row2->colB + square7->row2->colC + 
    square8->row2->colD + square9->row2->colD + square10->row3->colA + square11->row3->colB + 
    square12->row3->colC + square13->row3->colD + square14->row3->colE + square15->row4->colA + 
    square16->row4->colB + square17->row4->colC + square18->row4->colD + square19->row4->colE + 
    square20->row5->colA + square21->row5->colB + square22->row5->colC + square23->row5->colD + 
    square24->row5->colE

  -- chess pieces
  P = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9
  N = N0 + N1 + N2 + N3
  B = B0 + B1 + B2 + B3
  R = R0 + R1 + R2 + R3
  Q = Q0 + Q1
  K = K0 + K1

  piece = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + N0 + N1 + N2 + N3 + 
    B0 + B1 + B2 + B3 + R0 + R1 + R2 + R3 + Q0 + Q1 + K0 + K1

  -- color 
  Black = Black0 
  White = White0
  Color = Black0 + White0
  
  pieces = Black0->P0 + Black0->P1 + Black0->P2 + Black0->P3 + Black0->P4 + White0->P5 + 
    White0->P6 + White0->P7 + White0->P8 + White0->P9 + Black0->N0 + Black0->N1 + 
    White0->N2 + White0->N3 + Black0->B0 + Black0->B1 + White0->B2 + White0->B3 + 
    Black0->R0 + Black0->R1 + White0->R2 + White0->R3 + Black0->Q0 + White0->Q1 + 
    Black0->K0 + White0->K1
}

-- tests for structual soundness 
/* test expect {
  -- an empty board that is correctly constructed is structually sound 
  emptyBoardIsStructuralTest : {
    structural
  } for emptyBoard is sat

  -- structural catches when squares don't have unique coordinates 
  doubleMapBoardIsNotStructuralTest : {
    structural
  } for doubleMapBoard is unsat
} **/

------------------ FORMAL STATE TESTS --------------------

-- state with just one piece 
inst rookieMove {
  emptyBoard -- board setup 
  pc = square0->R0
  sq = R0->square0
  moves = R0->square1 + R0->square2 + R0->square3 + R0->square4 + R0->square5 + R0->square10 + R0->square15 + R0->square20
}

-- state that doesn't keep track of moves (should be unsat)
inst noMovesState {
  emptyBoard -- board setup 
  pc = square1->B1
  sq = B1->square1 
  no moves 
}

-- state with correct moves for 2+ pieces/interactions 
inst interactingPiecesState {
  emptyBoard -- board setup 
  pc = square0->K0 + square24->K1 + square1->R0
  sq = K0->square0 + K1->square24 + B0->square1
  moves = K0->square6 + K0->square5 + K1->square19 + K1->square23 + K1->square18 + 
    R0->square6 + R0->square11 + R0->square16 + R0->square21 + R0->square2 + R0->square3 + R0->square4
}

-- knight moves
inst knight {
  emptyBoard
  pc = square0 -> N0 + square12 -> N1
  sq = N0 -> square0 + N1 -> square12
  moves = N0 -> square11 + N0 -> square7 + N1 -> square21 + N1 -> square23 + N1 -> square19 + N1 -> square9 + N1 -> square3 + N1 -> square1 + N1 -> square5 + N1 -> square15
}

-- king moves
inst king {
  emptyBoard
  pc = square0 -> K1 + square12 -> K0
  sq = K1 -> square0 + K0 -> square12 
  moves = K1 -> square1 + K1 -> square5 + K1 -> square6 + K0 -> square16 + K0 -> square17 + K0 -> square18 + K0 -> square13 + K0 -> square8 + K0 -> square7 + K0 -> square11
}
-- bishop moves
inst bishop {
  emptyBoard
  pc = square12->B0 + square6->B1
  sq = B0->square12 + B1->square6
  moves = B0->square20 + B0->square16 + B0->square24 + B0->square18 + B0->square4 + B0->square8 + B1->square10 + B1->square2 + B1->square0
}

inst pawn {
  emptyBoard
  pc = square12->P1 + square6->P5
  sq = P1->square12 + P5->square6
  moves = P5->square16 + P5->square11 + P5->square12 + P1->square6 + P1->square7
}

-- a king makes a benign move
inst generalMove1 {
    emptyBoard

    -- first state
    pc = square13->K0 + square24->K1 + square4->R0
    sq = K0->square13 + K1->square24 + R0->square4

    -- second state
    pc' = square14->K0 + square24->K1 + square4->R0
    sq' = K0->square14 + K1->square24 + R0->square4
}

-- two pieces switch places 
inst generalMove2 {
    emptyBoard

    -- first state
    pc = square13->K0 + square24->K1 + square4->R0 + square5->R1
    sq = K0->square13 + K1->square24 + R0->square4 + R1->square5

    -- second state
    pc' = square14->K0 + square24->K1 + square5->R0 + square4->R1
    sq' = K0->square14 + K1->square24 + R1->square5 + R0->square4
}

-- one piece tries to move to its teammate's spot
inst generalMove3 {
    emptyBoard

    -- first state
    pc = square13->K0 + square24->K1 + square4->R0 + square5->R1
    sq = K0->square13 + K1->square24 + R0->square4 + R1->square5

    -- second state
    pc' = square14->K0 + square24->K1 + square5->R0
    sq' = K0->square14 + K1->square24 + R0->square5 
}

-- a capture occurs (Rook takes other Rook)
inst generalMove4 {
    emptyBoard

    -- first state
    pc = square13->K0 + square24->K1 + square4->R0 + square5->R2
    sq = K0->square13 + K1->square24 + R0->square4 + R2->square5

    -- second state
    pc' = square14->K0 + square24->K1 + square4->R2
    sq' = K0->square14 + K1->square24 + R2->square4
}

-- queen moves
inst queen {
  emptyBoard
  pc = square12->Q0 + square7->Q1
  sq = Q0->square12 + Q1->square7
  moves = Q0->square20 + Q0->square16 + Q0->square22 + Q0->square17 + Q0->square24 + Q0->square18 + Q0->square14 + Q0->square13 + Q0->square4 + Q0->square8 + Q0->square7 + Q0->square0 + Q0->square6 + Q0->square10 + Q0->square11 + Q1->square15 + Q1->square11 + Q1->square12 + Q1->square19 + Q1->square13 + Q1->square9 + Q1->square8 + Q1->square3 + Q1->square2 + Q1->square1 + Q1->square5 + Q1->square6
}

-- capture
inst pawnCapture {
  pawn
  pc' = square12->P5
  sq' = P5->square12
  moves = P5->square17
}

-- twoRookMate
inst twoRookMate {
  emptyBoard
  pc = square0->K0 + square4->R2 + square8->R3
  sq = K0->square0 + R2->square4 + R3->square8
  moves = R2->square0 + R2->square1 + R2->square2 + R2->square3 + R2->square24 + R2->square19 + R2->square14 + R2->square9 + R3->square5 + R3->square6 + R3->square7 + R3->square9 + R3->square23 + R3->square18 + R3->square13 + R3->square3
}

-- rookAndKing
inst rookAndKing {
  emptyBoard
  pc = square11->K1 + square1->K0 + square4->R3
  sq = K1->square11 + K0->square1 + R3->square4
  moves = K1->square16 + K1->square17 + K1->square12 + K1->square17 + K1->square10 + K1->square15 + R3->square1 + R3->square2 + R3->square3 + R3->square24 + R3->square19 + R3->square14 + R3->square9
}

-- tests for state move soundness 
test expect {
  /* -- an empty board that is correctly constructed is structually sound -- */
  // rookieMoveOkTest : {
  //   allMoves
  // } for rookieMove is sat
  
  // /* -- a state with pieces and without moves doesn't work -- */
  // noMovesTest : {
  //   allMoves
  // } for noMovesState is unsat

  // // /* -- makes sure that moves with many pieces (mimicking a real board) are valid -- */
  // interactingPiecesTest : {
  //   allMoves
  // } for interactingPiecesState is sat // CHECK!!!! **/ -- WHY DID I ONLY GET STATES WITH NO MOVES  

  // knightTest : {
  //   allMoves
  // } for knight is sat

  // kingTest : {
  //   allMoves
  // } for king is sat

  // bishopTest : {
  //   allMoves
  // } for bishop is sat

  // pawnTest : {
  //   allMoves
  // } for pawn is sat


-- benign move
  generalMove1Test: {
      generalMove1
      some p : piece | generalMove[p]
  } is sat
  -- two pieces switch places
  generalMove2Test: {
      generalMove2
      some p : piece | generalMove[p]
  } is sat
  -- one piece tries to capture own teammate
  generalMove3Test: {
      generalMove3
      some p : piece | generalMove[p]
  } is sat
  -- one piece captures another (validly)
  generalMove4Test: {
      generalMove4
      some p : piece | generalMove[p]
  } is sat


  queenTest : {
    allMoves
  } for queen is sat

  twoRookMateTest : {
    checkmate
  } for twoRookMate is sat

  rookAndKingTest : {
    checkmate
  } for rookAndKing is sat
  
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
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 B, exactly 2 K -- sat because 2 B checkmate poss.
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 1 B, exactly 1 N, exactly 2 K -- sat
run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 R, exactly 2 K -- sat 
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 4 piece, exactly 2 R, exactly 2 K -- sat
// run {mate1} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 Q, exactly 2 K -- sat