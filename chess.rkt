#lang forge

option problem_type temporal 
option max_tracelength 10 -- NEEDED! default is 5. need to be able to find the whole lasso.
option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

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
one sig colE extends col {} -- disabled for performance reasons
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

-- Represents color of pieces 
abstract sig Color {
  pieces: set piece
}

one sig Black extends Color {}
one sig White extends Color {}

-- preds for color membership
pred colorMembership { -- TODO UNSAT
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

-- Experimental
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

-- Pawn related preds --------------------------
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

-- King related preds --------------------------
pred validKings { -- should only and always have 2 kings.
  #(K) = 2
  all k: K | {
    some pc.k
  }
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
      // s not in (Color - (pieces.k)).pieces.(moves')
    }
  }
}

-- Bishop related preds --------------------------
pred BMoves[b: B] {
  -- need to add legality for king safety. If king in danger, none, else, ...?
  all s: square | { -- For all squares, ...
    s in b.moves iff { -- square is in bishop's legal moves iff ...
      some s.pc implies not isSameColor[b, s.pc]
      validMovesForBishop[s, b]
    }
  }
}

pred validMovesForBishop[a: square, b: piece] {  -- should be B, but piece to allow reuse with Queen 
  -- true for square a if it is on a diagonal square that is not blocked
    (a in pcprDiags[pc.b] and (no p: piece | {pc.p in pcprDiags[pc.b] and pc.p in ncnrDiags[a]})) or
    (a in pcnrDiags[pc.b] and (no p: piece | {pc.p in pcnrDiags[pc.b] and pc.p in ncprDiags[a]})) or
    (a in ncprDiags[pc.b] and (no p: piece | {pc.p in ncprDiags[pc.b] and pc.p in pcnrDiags[a]})) or
    (a in ncnrDiags[pc.b] and (no p: piece | {pc.p in ncnrDiags[pc.b] and pc.p in pcprDiags[a]}))
}

-- Knight related preds ------------------------------
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

-- Rook related preds --------------------------
pred RMoves[r: R] {
  all s: square | {
    s in r.moves iff {
      some s.pc implies not isSameColor[r, s.pc]
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

-- Queen related preds -------------------------

pred QMoves[q: Q] {
  all s: square | {
    s in q.moves iff {
      some s.pc implies not isSameColor[q, s.pc]
      validMovesForRook[s, q] or validMovesForBishop[s, q]
    }
  }
}

--- General move-related preds --------------
pred generalMove[p : piece] {
  some s : square | {
    s in p.moves
    some s.pc implies {
      pc' = pc - (pc.p -> p) - (s -> s.pc) + (s -> p)
    } else {
      pc' = pc - (pc.p -> p) + (s -> p) 
    }
  }
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

pred checkmate {
  some k : K | {
    --TODO: Check king color
    -- A state where the king is under attack
    // no k.moves
    some p1 : piece {
      not isSameColor[k, p1]
      pc.k in p1.moves
      pc.p1 not in (pieces.k).pieces.moves
      no p3 : piece | {
        // generalMove[p3] implies after not inCheck[k]
        isSameColor[k, p3]
      }
    }
    -- To block:
      -- Attacking piece is knight or there is no piece that can get between that piece and the king square
      -- Same way we check for obstructions (expensive)
      -- p1 in the after state, p1 is no longer attacking k (temporality issue)
      -- Not a pawn or a knight
      -- One of the moves of some piece is a square in the set of moves of the attacking piece and 
    -- And afterwards the king is still under attack and has no moves
    -- Would this be able 
    after {
      no k.moves
      some p2 : piece {
        not isSameColor[k, p2]
        pc.k in p2.moves
      }
    }
  }
}

// pred validBoard { -- position legality 
//   // validKings
//   piecesToSquares
//   colorMembership
// }

pred whiteMove {
  some p: White.pieces | { generalMove[p] } 
}

pred blackMove {
  some p: Black.pieces | { generalMove[p] }
}

-- turns
pred turns {
  whiteMove implies { after (blackMove and not whiteMove)}
  blackMove implies { after (whiteMove and not blackMove)}
}

-- init state
pred init {
  // not checkmate
  whiteMove
  always turns
  colorMembership
  all p: piece | {
    some p.sq
  }
}

-- traces 
pred traces {
  init
  always {
    colorMembership
    structural
    allMoves
  }
  // eventually checkmate
}

-- generates a chess puzzle 
pred generatePuzzle {
  traces until checkmate
  always {
    structural
    allMoves 
    }
}

pred scenario {
  // #(Black.pieces & R) = 1
  // #(White.pieces & R) = 1
  // #(Black.pieces & K) = 1
  // #(White.pieces & K) = 1
  #(Black.pieces & R) = 1
  #(White.pieces & R) = 1
  #(White.pieces & K) = 1
  // all r : R | {
  //   pc.r.coord.col = row1
  // }
}

-- generates a 5x5 board 
// run {traces and scenario} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 2 piece, exactly 1 R, exactly 1 P
run {traces and scenario} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 2 R, exactly 1 K

// inst kingCorner {
//   -- rows and cols
//   colA = colA0
//   colB = colB0
//   colC = colC0
//   colD = colD0
//   colE = colE0
//   colF = colF0
//   colG = colG0
//   colH = colH0

//   row1 = row10
//   row2 = row20
//   row3 = row30
//   row4 = row40
//   row5 = row50
//   row6 = row60
//   row7 = row70
//   row8 = row80

//   row = row10 + row20 + row30 + row40 + row50 + row60 + row70 + row80
//   col = colA0 + colB0 + colC0 + colD0 + colE0 + colF0 + colG0 + colH0

//   c_prev = colB0->colA0 + colC0->colB0 + colD0->colC0 + colE0->colD0 + colF0->colE0 + colG0->colF0 + colH0->colG0
//   c_next = colA0->colB0 + colB0->colC0 + colC0->colD0 + colD0->colE0 + colE0->colF0 + colF0->colG0 + colG0->colH0
//   r_prev = row20->row10 + row30->row20 + row40->row30 + row50->row40 + row60->row50 + row70->row60 + row80->row70
//   r_next = row10->row20 + row20->row30 + row30->row40 + row40->row50 + row50->row60 + row60->row70 + row70->row80

//   -- squares 
//   square = square0 + square1 + square2 + square3 + square4 + square5 + 
//     square6 + square7 + square8 + square9 + square10 + square11 + 
//     square12 + square13 + square14 + square15 + square16 + square17 + 
//     square18 + square19 + square20 + square21 + square22 + square23 + 
//     square24 + square25 + square26 + square27 + square28 + square29 + 
//     square30 + square31 + square32 + square33 + square34 + square35 + 
//     square36 + square37 + square38 + square39 + square40 + square41 + 
//     square42 + square43 + square44 + square45 + square46 + square47 + 
//     square48 + square49 + square50 + square51 + square52 + square53 + 
//     square54 + square55 + square56 + square57 + square58 + square59 + 
//     square60 + square61 + square62 + square63
  
//   coord = square0->row1->colA + square1->row1->colB + square2->row1->colC + square3->row1->colD + 
//     square4->row1->colE + square5->row1->colF + square6->row1->colG + square7->row1->colH + 
//     square8->row2->colA + square9->row2->colB + square10->row2->colC + square11->row2->colD + 
//     square12->row2->colE + square13->row2->colF + square14->row2->colG + square15->row2->colH + 
//     square16->row3->colA + square17->row3->colB + square18->row3->colC + square19->row3->colD + 
//     square20->row3->colE + square21->row3->colF + square22->row3->colG + square23->row3->colH + 
//     square24->row4->colA + square25->row4->colB + square26->row4->colC + square27->row4->colD + 
//     square28->row4->colE + square29->row4->colF + square30->row4->colG + square31->row4->colH + 
//     square32->row5->colA + square33->row5->colB + square34->row5->colC + square35->row5->colD + 
//     square36->row5->colE + square37->row5->colF + square38->row5->colG + square39->row5->colH + 
//     square40->row6->colA + square41->row6->colB + square42->row6->colC + square43->row6->colD + 
//     square44->row6->colE + square45->row6->colF + square46->row6->colG + square47->row6->colH + 
//     square48->row7->colA + square49->row7->colB + square50->row7->colC + square51->row7->colD + 
//     square52->row7->colE + square53->row7->colF + square54->row7->colG + square55->row7->colH + 
//     square56->row8->colA + square57->row8->colB + square58->row8->colC + square59->row8->colD + 
//     square60->row8->colE + square61->row8->colF + square62->row8->colG + square63->row8->colH

//   -- chess pieces
//   P = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15
//   N = N0 + N1 + N2 + N3
//   B = B0 + B1 + B2 + B3
//   R = R0 + R1 + R2 + R3
//   Q = Q0 + Q1
//   K = K0 + K1

//   piece = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15 + 
//     N0 + N1 + N2 + N3 + B0 + B1 + B2 + B3 + R0 + R1 + R2 + R3 + Q0 + Q1 + K0 + K1

//   -- color 
//   Black = Black0 
//   White = White0
//   Color = Black0 + White0
  
//   pieces = Black0->P0 + Black0->P1 + Black0->P2 + Black0->P3 + Black0->P4 + Black0->P5 + 
//     Black0->P6 + Black0->P7 + White0->P8 + White0->P9 + White0->P10 + White0->P11 + 
//     White0->P12 + White0->P13 + White0->P14 + White0->P15 + Black0->N0 + Black0->N1 + 
//     White0->N2 + White0->N3 + Black0->B0 + Black0->B1 + White0->B2 + White0->B3 + 
//     Black0->R0 + Black0->R1 + White0->R2 + White0->R3 + Black0->Q0 + White0->Q1 + 
//     Black0->K0 + White0->K1

//   pc = square0 -> K1
//   sq = K1 -> square0
//   moves = K1 -> square8 + K1 -> square9 + K1 -> square1
// }

// inst twoSquaresWithSameCoords {
//   -- rows and cols
//   colA = colA0
//   colB = colB0
//   colC = colC0
//   colD = colD0
//   colE = colE0
//   colF = colF0
//   colG = colG0
//   colH = colH0

//   row1 = row10
//   row2 = row20
//   row3 = row30
//   row4 = row40
//   row5 = row50
//   row6 = row60
//   row7 = row70
//   row8 = row80

//   row = row10 + row20 + row30 + row40 + row50 + row60 + row70 + row80
//   col = colA0 + colB0 + colC0 + colD0 + colE0 + colF0 + colG0 + colH0

//   c_prev = colB0->colA0 + colC0->colB0 + colD0->colC0 + colE0->colD0 + colF0->colE0 + colG0->colF0 + colH0->colG0
//   c_next = colA0->colB0 + colB0->colC0 + colC0->colD0 + colD0->colE0 + colE0->colF0 + colF0->colG0 + colG0->colH0
//   r_prev = row20->row10 + row30->row20 + row40->row30 + row50->row40 + row60->row50 + row70->row60 + row80->row70
//   r_next = row10->row20 + row20->row30 + row30->row40 + row40->row50 + row50->row60 + row60->row70 + row70->row80

//   -- squares 
//   square = square0 + square1 + square2 + square3 + square4 + square5 + 
//     square6 + square7 + square8 + square9 + square10 + square11 + 
//     square12 + square13 + square14 + square15 + square16 + square17 + 
//     square18 + square19 + square20 + square21 + square22 + square23 + 
//     square24 + square25 + square26 + square27 + square28 + square29 + 
//     square30 + square31 + square32 + square33 + square34 + square35 + 
//     square36 + square37 + square38 + square39 + square40 + square41 + 
//     square42 + square43 + square44 + square45 + square46 + square47 + 
//     square48 + square49 + square50 + square51 + square52 + square53 + 
//     square54 + square55 + square56 + square57 + square58 + square59 + 
//     square60 + square61 + square62 + square63
  
//   coord = square0->row1->colA + square1->row1->colA + square2->row1->colC + square3->row1->colD + 
//     square4->row1->colE + square5->row1->colF + square6->row1->colG + square7->row1->colH + 
//     square8->row2->colA + square9->row2->colB + square10->row2->colC + square11->row2->colD + 
//     square12->row2->colE + square13->row2->colF + square14->row2->colG + square15->row2->colH + 
//     square16->row3->colA + square17->row3->colB + square18->row3->colC + square19->row3->colD + 
//     square20->row3->colE + square21->row3->colF + square22->row3->colG + square23->row3->colH + 
//     square24->row4->colA + square25->row4->colB + square26->row4->colC + square27->row4->colD + 
//     square28->row4->colE + square29->row4->colF + square30->row4->colG + square31->row4->colH + 
//     square32->row5->colA + square33->row5->colB + square34->row5->colC + square35->row5->colD + 
//     square36->row5->colE + square37->row5->colF + square38->row5->colG + square39->row5->colH + 
//     square40->row6->colA + square41->row6->colB + square42->row6->colC + square43->row6->colD + 
//     square44->row6->colE + square45->row6->colF + square46->row6->colG + square47->row6->colH + 
//     square48->row7->colA + square49->row7->colB + square50->row7->colC + square51->row7->colD + 
//     square52->row7->colE + square53->row7->colF + square54->row7->colG + square55->row7->colH + 
//     square56->row8->colA + square57->row8->colB + square58->row8->colC + square59->row8->colD + 
//     square60->row8->colE + square61->row8->colF + square62->row8->colG + square63->row8->colH

//   -- chess pieces
//   P = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15
//   N = N0 + N1 + N2 + N3
//   B = B0 + B1 + B2 + B3
//   R = R0 + R1 + R2 + R3
//   Q = Q0 + Q1
//   K = K0 + K1

//   piece = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15 + 
//     N0 + N1 + N2 + N3 + B0 + B1 + B2 + B3 + R0 + R1 + R2 + R3 + Q0 + Q1 + K0 + K1

//   -- color 
//   Black = Black0 
//   White = White0
//   Color = Black0 + White0
  
//   pieces = Black0->P0 + Black0->P1 + Black0->P2 + Black0->P3 + Black0->P4 + Black0->P5 + 
//     Black0->P6 + Black0->P7 + White0->P8 + White0->P9 + White0->P10 + White0->P11 + 
//     White0->P12 + White0->P13 + White0->P14 + White0->P15 + Black0->N0 + Black0->N1 + 
//     White0->N2 + White0->N3 + Black0->B0 + Black0->B1 + White0->B2 + White0->B3 + 
//     Black0->R0 + Black0->R1 + White0->R2 + White0->R3 + Black0->Q0 + White0->Q1 + 
//     Black0->K0 + White0->K1

//   no pc 
//   no sq 
//   no moves
// }

// inst emptyBoard {
//   -- rows and cols
//   colA = colA0
//   colB = colB0
//   colC = colC0
//   colD = colD0
//   colE = colE0
//   colF = colF0
//   colG = colG0
//   colH = colH0

//   row1 = row10
//   row2 = row20
//   row3 = row30
//   row4 = row40
//   row5 = row50
//   row6 = row60
//   row7 = row70
//   row8 = row80

//   row = row10 + row20 + row30 + row40 + row50 + row60 + row70 + row80
//   col = colA0 + colB0 + colC0 + colD0 + colE0 + colF0 + colG0 + colH0

//   c_prev = colB0->colA0 + colC0->colB0 + colD0->colC0 + colE0->colD0 + colF0->colE0 + colG0->colF0 + colH0->colG0
//   c_next = colA0->colB0 + colB0->colC0 + colC0->colD0 + colD0->colE0 + colE0->colF0 + colF0->colG0 + colG0->colH0
//   r_prev = row20->row10 + row30->row20 + row40->row30 + row50->row40 + row60->row50 + row70->row60 + row80->row70
//   r_next = row10->row20 + row20->row30 + row30->row40 + row40->row50 + row50->row60 + row60->row70 + row70->row80

//   -- squares 
//   square = square0 + square1 + square2 + square3 + square4 + square5 + 
//     square6 + square7 + square8 + square9 + square10 + square11 + 
//     square12 + square13 + square14 + square15 + square16 + square17 + 
//     square18 + square19 + square20 + square21 + square22 + square23 + 
//     square24 + square25 + square26 + square27 + square28 + square29 + 
//     square30 + square31 + square32 + square33 + square34 + square35 + 
//     square36 + square37 + square38 + square39 + square40 + square41 + 
//     square42 + square43 + square44 + square45 + square46 + square47 + 
//     square48 + square49 + square50 + square51 + square52 + square53 + 
//     square54 + square55 + square56 + square57 + square58 + square59 + 
//     square60 + square61 + square62 + square63
  
//   coord = square0->row1->colA + square1->row1->colB + square2->row1->colC + square3->row1->colD + 
//     square4->row1->colE + square5->row1->colF + square6->row1->colG + square7->row1->colH + 
//     square8->row2->colA + square9->row2->colB + square10->row2->colC + square11->row2->colD + 
//     square12->row2->colE + square13->row2->colF + square14->row2->colG + square15->row2->colH + 
//     square16->row3->colA + square17->row3->colB + square18->row3->colC + square19->row3->colD + 
//     square20->row3->colE + square21->row3->colF + square22->row3->colG + square23->row3->colH + 
//     square24->row4->colA + square25->row4->colB + square26->row4->colC + square27->row4->colD + 
//     square28->row4->colE + square29->row4->colF + square30->row4->colG + square31->row4->colH + 
//     square32->row5->colA + square33->row5->colB + square34->row5->colC + square35->row5->colD + 
//     square36->row5->colE + square37->row5->colF + square38->row5->colG + square39->row5->colH + 
//     square40->row6->colA + square41->row6->colB + square42->row6->colC + square43->row6->colD + 
//     square44->row6->colE + square45->row6->colF + square46->row6->colG + square47->row6->colH + 
//     square48->row7->colA + square49->row7->colB + square50->row7->colC + square51->row7->colD + 
//     square52->row7->colE + square53->row7->colF + square54->row7->colG + square55->row7->colH + 
//     square56->row8->colA + square57->row8->colB + square58->row8->colC + square59->row8->colD + 
//     square60->row8->colE + square61->row8->colF + square62->row8->colG + square63->row8->colH

//   -- chess pieces
//   P = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15
//   N = N0 + N1 + N2 + N3
//   B = B0 + B1 + B2 + B3
//   R = R0 + R1 + R2 + R3
//   Q = Q0 + Q1
//   K = K0 + K1

//   piece = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12 + P13 + P14 + P15 + 
//     N0 + N1 + N2 + N3 + B0 + B1 + B2 + B3 + R0 + R1 + R2 + R3 + Q0 + Q1 + K0 + K1

//   -- color 
//   Black = Black0 
//   White = White0
//   Color = Black0 + White0
  
//   pieces = Black0->P0 + Black0->P1 + Black0->P2 + Black0->P3 + Black0->P4 + Black0->P5 + 
//     Black0->P6 + Black0->P7 + White0->P8 + White0->P9 + White0->P10 + White0->P11 + 
//     White0->P12 + White0->P13 + White0->P14 + White0->P15 + Black0->N0 + Black0->N1 + 
//     White0->N2 + White0->N3 + Black0->B0 + Black0->B1 + White0->B2 + White0->B3 + 
//     Black0->R0 + Black0->R1 + White0->R2 + White0->R3 + Black0->Q0 + White0->Q1 + 
//     Black0->K0 + White0->K1

//   no pc 
//   no sq 
//   no moves
// }

// test expect {
//   sanityCheck : {
//     structural
//   } for emptyBoard is sat

//   notFunctional : {
//     functionalBoard
//   } for twoSquaresWithSameCoords is unsat

//   functional : {
//     functionalBoard
//   } for emptyBoard is sat
// }

// run kingCorner

// test expect {
//   restrictedKing : {
//     allMoves
//   } for kingCorner is sat
// }