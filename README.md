# Forge-chess: a Chess Endgame Simulator 
This project simulates 
1. possible move combinations at the end of a chess game and 
2. possible checkmate-in-one states under some set of common endgame conditions.

---

#### Structure
The model, written in `chess.rkt`, is structured into a series of sigs, preds, run statements, and tests.

**Sigs:** We have sigs for each row and column. The sig square stores a board square’s coordinates and piece. To represent pieces, we have an abstract sig that is extended by a sig for each type of piece (B for bishop, K for king, etc.). The pieces store their square and a set of all valid moves. We have sigs for Black and White, the colors of the teams; the pieces set stores relations between color and piece. 

**Preds:** Our code consists of several categories of preds:
* helpers to find square relationships (including adjacentTo)
* color relationships(colorMembership, isSameColor) 
* structural + helpers for structural (like functionalBoard, which maintains square to coord relations) which maintain board structure
* Moves/validmoves for each piece
* King-specific conditions (kingSafety, validKings, inCheck, twoChecks)
* generalMove for any move or state transition
* checkmate
* whiteMove, blackMove for turns
* state and state-transition related (init, traces)

Details about the preds are commented in the code. 

**Functions:**
We had a handful of helper functions to facilitate determining square relations. These functions (allDiags, prevRow, etc.) get the related row, col, or square relative to a given input square. 

**Run statements:** 
We have two sets of run statements. The first set shows randomly selected examples of move sequences. The second set shows a single move that results in checkmate. 

**Testing/verification:** Testing is separated in sections and commented. 

#### Our model proved 
* that a model of a set of moves in a late-stage chess game can help chess learners evaluate and learn from the pitfalls of the moves
* that generating valid/invalid states and sequences of moves from a set of conditions can be useful for verifying certain truths about chess moves or testing chess software
    * more specifically, we can use our code to prove that checkmate can only happen in certain conditions (i.e. when there are 2 knights on the board, and not when there is one knight) 

#### Tradeoffs we made
In some cases, we chose to store extra information, such as bidirectional mapping between squares and pieces, which increased our runtimes, but helped with ease of writing preds. We chose to hardcode our rows and columns for ease of testing.

In other cases, we abandoned certain sigs (such as our Board) to save space. 

We initially thought hardcoding our white and black pieces would help us with visualization and piece membership, but we turned to abstraction to reduce the overall number of sigs. 

We also talked about the idea of each square storing information on its NE, SE, SW, and NW diagonals. Although this would result in easier predicates for diagonal moves, we decided that the space usage and relation computation would be too costly. 

To easily represent moves and transitions between states, we decided that each piece would have a set of legal moves. This was especially useful for the King since the King can’t move into a square that’s covered by an enemy piece, whereas other pieces don’t have this restriction. 

Since chess is a game involving discrete states, it seemed natural to use Electrum, but this posed an issue for us when writing our checkmate predicate. We wanted a predicate that would say “for a player to be in checkmate, all legal moves for such player must result in that player’s king staying in check”, but it became easier to separate the tasks into generation of a sequence of valid moves and generation of checkmate-in-one states. 

#### Assumptions about scope & limits of the model
* Timewise, running the model on larger and larger boards makes it slower
* Scope: had to cut back on space to allow for 8x8 to be possible, more focus on late game positions with fewer pieces and less legal moves
* Limits: Diagonal computation is particularly expensive, so positions involving queens or bishops are very slow to compute and better reserved for a 5x5 board.

#### Reflection on Goals vs. Proposal - were plans unrealistic, or was anything deemed unrealistic doable?
Many of our goals remained consistent. Considering the smaller scope of positions we’re targeting, we decided to forego moves such as en passant and castling, which depend on the current state as well as prior states. When we first proposed this idea, we knew it would be unrealistic to model an entire game from start to finish, so we limited our model to the endgame. Although this helped with our space concerns, we still ran into a number of optimization related problems that we had to overcome or compromise with. 

#### Known Bugs
Some scenarios can result in incorrect checkmate-in-ones. To be precise, cases where the piece delivering checkmate can be interfered with (via capturing or blocking) can be incorrectly declared as checkmate by the program.

#### Future Plans
With more time, we would want to focus on optimizations to decrease runtime for the 8x8 board.
We would also want to integrate checkmates with turns; ideally, creating a sequence of turns must lead to checkmate (also mentioned in our reach goal).

#### How to understand an instance of the model + custom visualization

An instance of a chess position and following move(s) is generated in Sterling. Running the provided script.js will display a typical chess board (albeit truncated, if using 5x5). It can be interpreted like any other chess board. 

