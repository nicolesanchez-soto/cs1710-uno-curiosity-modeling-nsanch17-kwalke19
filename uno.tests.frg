#lang forge/froglet
open "uno.frg"

test suite for initGame {
  
      // Example test: A valid initial game state
    example validGameInit is { initGame[`m0] } for {
        Move = `m0
        Player = `p0 + `p1
        Card = `c0 + `c1 + `c2 + `c3 + `c4 + `c5 + `c6 + `c7 + `c8 + `c9 + `c10 + `c11 + `c12 + `c13 + `c14 + `c15 + `c16 + `c17 + `c18
        GameState = `gs

        // One player is chosen as the starting player
        `gs.currentPlayer = `m0 -> `p0 
        
        // No pending actions at the start (omitting explicit empty set)
        // No cards in the discard pile (omitting explicit empty set)

    }
}