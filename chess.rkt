#lang forge

option problem_type temporal 
option max_tracelength 5 -- NEEDED! default is 5. need to be able to find the whole lasso.
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
sig R extends piece {} -- rook
sig N extends piece {} -- knight
sig K extends piece {} -- king

-- Represents color of pieces 
abstract sig Color {
  pieces: set piece
}

one sig Black extends Color {}
one sig White extends Color {}

one sig Turn {
  var current: one Color
}

-- preds for color membership
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

-- STRUCTURE + VALIDITY ----------------------
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

-- King related preds --------------------------
pred validKings { -- should only and always have 2 kings.
  #(K) = 2
  all k: K | {
    some pc.k
  }
  -- TODO enable later
  one k: K | {
    k in White.pieces
  }
  one k: K | {
    k in Black.pieces
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

// pred noAdjacentKings[] { 
//   some k1 : K | {
//     some k2 : K - k1 | {
//       adjacentTo[k1, k2]
//     }
//   }
// }

-- King must be on the board
pred KMoves[k : K] {
  some pc.k
  all s : square | {
    s in k.moves iff {
      adjacentTo[pc.k, s]
      no k2 : K - k | { adjacentTo[s, pc.k2] }
      some s.pc implies not isSameColor[k, s.pc]
      no p : piece | {
        s in p.moves
        not isSameColor[k, p]
      }
      // s not in (Color - (pieces.k)).pieces.(moves')
    }
  }
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

--- General move-related preds --------------

-- also need to consider: white cannot move unless black moves b4 (before?), vice versa
// -- KNOWN BUGS:
pred generalMove[p : piece] {
  -- some square before 
  some p.sq
  -- some square after 
  some p.sq' 
  -- valid move 
  p.sq' in p.moves
  -- captured 
  some s : square | { ((s = p.sq' and some s.pc) and (not isSameColor[s.pc, p])) => {
      s.pc not in square.pc'
      square.pc - s.pc = square.pc'
    } else {
      square.pc = square.pc'
    }
  }
  all other : piece - p | {
    not other.sq = p.sq' => {
      other.sq' = other.sq
    }
    other.sq = p.sq' => {
      // other.sq' = other.sq or no other.sq' -- TODO what's going on here? 
      no other.sq'
    }
  }
  -- TODO verify new addition. Prevents king from being attacked after move.
  after { no k: K | { isSameColor[k, p] and inCheck[k] }}
}

pred checkmate {
  some k : K | {
    --TODO: Check king color
    -- A state where the king is under attack
    // no k.moves
    some p1 : piece {
      not isSameColor[k, p1] -- piece is not same color
      pc.k in p1.moves -- king under attack
      // not generalMove[k] -- king can't move anywhere
      // pc.p1 not in (pieces.k).pieces.moves -- attacking piece not capturable
      no p3 : piece | { -- no piece that can move and end the threat
        generalMove[p3] //implies after not inCheck[k]
        // isSameColor[k, p3] -- should now be covered in generalMove itself + turn restriction?
      }
    }
    no k.moves
    -- To block:
      -- Attacking piece is knight or there is no piece that can get between that piece and the king square
      -- Same way we check for obstructions (expensive)
      -- p1 in the after state, p1 is no longer attacking k (temporality issue)
      -- Not a pawn or a knight
      -- One of the moves of some piece is a square in the set of moves of the attacking piece and 
    -- And afterwards the king is still under attack and has no moves
    -- Would this be able 
  }
}

-- game over 
pred gameOver {
  sq = sq'
  pc = pc'
}

-- ensures all pieces maintain valid moves 
pred allMoves {
  all r: R | { RMoves[r] }
  all k: K | { KMoves[k] }
  all n: N | { NMoves[n] }
}

pred whiteMove {
  one p: piece | { generalMove[p] and p in White.pieces } 
}

pred blackMove {
  one p: piece | { generalMove[p] and p in Black.pieces }
}

pred checkAndNotMove {
  whiteMove implies {
    no k: K | { k in Black.pieces and inCheck[k] }
  }
  blackMove implies {
    no k: K | { k in White.pieces and inCheck[k] }
  }
}

-- init state
pred init {
  // not checkmate
  whiteMove
  all p: piece | {
    some p.sq
  }
}

-- turns
pred turns {
  whiteMove implies { after ((blackMove and not whiteMove))}
  blackMove implies { after ((whiteMove and not blackMove))}
}

-- traces 
pred traces {
  init
  validKings
  always {
    colorMembership
    structural
    allMoves
    checkAndNotMove
  }
  after checkmate 
}

pred validKingMoves {
  all k : K | {
    KMoves[k]
  }
}

pred scenario {
  #(White.pieces & R) = 2
  #(Black.pieces & K) = 1
  all r : R | {
    pc.r.coord.col = row1
  }
}

-- generates a standard board 
// run {traces} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 N, exactly 2 K -- unsat because 1 N checkmate impossible.
run {traces} for exactly 5 col, exactly 5 row, exactly 25 square, exactly 3 piece, exactly 1 R, exactly 2 K
