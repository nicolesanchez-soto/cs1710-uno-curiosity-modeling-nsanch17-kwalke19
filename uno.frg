#lang forge

-------------------------------------------------------------------------------
/*  UNO is a multi-player card game where the goal is to be the first player   
    to get rid of all your cards. Players take turns playing cards from their  
    hand that match either the color or number of the card on top of the       
    discard pile. The game includes number cards (0-9) in four colors (red,    
    blue, green, yellow), as well as special action cards like Skip, Reverse,  
    and Draw Two that affect gameplay. Wild cards can be played at any time    
    and allow the player to choose a new color. Wild Draw Four cards combine   
    this color-changing ability with forcing the next player to draw four      
    cards. Players must call "UNO" when they have one card left or face a      
    penalty. The game continues until a player has successfully played all      
    their cards.                                      
*/                     
-------------------------------------------------------------------------------

// Boolean signature for True/False values across the model
abstract sig Boolean {}
// Exactly one instance each of True and False
one sig True, False extends Boolean {}

// Move signature represents game state at a specific player's turn
sig Move {
    // Optional reference to the next move in sequence (may not exist if game ends)
    next: lone Move
}

// Color signature defines the UNO card colors
abstract sig Color {}
// Note: Simplified to 3 colors (missing Yellow) to reduce model complexity
one sig Red, Blue, Green extends Color {}

// Value signature defines all possible card values in UNO
abstract sig Value {}
// Simplified number cards (only 0-2 instead of 0-9)
one sig Zero, One, Two extends Value {}
// Action cards - simplified to only include Skip and DrawTwo
one sig Skip, DrawTwo extends Value {}
// Wild cards - both types included
one sig Wild, WildDrawFour extends Value {}

// Card signature defines structure of UNO cards
sig Card {
    // Optional color - Wild cards don't have predefined colors
    color: lone Color,
    // Every card must have a value
    value: one Value
}

// Central game state tracker - manages all aspects of the game
one sig GameState {
    // Track which cards are in the deck at each move (partial function mapping)
    deck: pfunc Move -> Card -> Boolean,
    // Track discard pile ordering with integer indices
    discard: pfunc Move -> Int -> Card,
    // Track which player's turn it is
    currentPlayer: pfunc Move -> Player -> Boolean,
    // Track which players are active in the game
    players: pfunc Move-> Player -> Boolean,
    // Track which cards are in each player's hand
    hands: pfunc Move -> Player -> Card -> Boolean,
    // Track color chosen when wild cards are played
    chosenColor: pfunc Move -> Card -> Color,
    // Track pending actions (from action cards)
    pendingAction: pfunc Move -> Value
}

// Player signature represents game participants
sig Player {}

// Predicate to ensure cards follow UNO rules
pred validCard[c: Card] {
    // Wild cards should have no color initially (color chosen when played)
    (c.value in Wild + WildDrawFour) implies no c.color
    // Non-wild cards must have exactly one color
    (c.value not in Wild + WildDrawFour ) implies some c.color
}

// Controls card distribution in the game - simplified for performance
pred validCardSpread{
    // One of each number card per color (instead of two in real UNO)
    all val: Zero + One + Two, c : Color |{
        #{card: Card | card.value = val and card.color = c} = 1
    } 

    // One of each action card per color (instead of two in real UNO)
    all v: Skip + DrawTwo, c: Color |
        #{card: Card | card.value = v and card.color = c} = 1 
 
    // Only 2 Wild cards of each type (instead of 4 in real UNO)
    #{card: Card | card.value = Wild} = 2
    #{card: Card | card.value = WildDrawFour} = 2
}

// Initialize a new game state
pred initGame[m0: Move] {
    // Ensure all cards follow UNO rules
    all c: Card | validCard[c]
    
    // Discard pile starts empty
    all i: Int, c: Card | no GameState.discard[m0][i]

    // Set first player as current (single player marked True)
    one p: Player | {
        GameState.currentPlayer[m0][p] = True
    }

    // No pending actions at start
    no GameState.pendingAction[m0]
}

// Deal initial cards to players
pred deal[m: Move] {
    // Ensure cards are distributed correctly per rules
    validCardSpread
    
    // Each player starts with exactly 7 cards
    all p: Player |
        #{ c: Card | GameState.hands[m][p][c] = True } = 7
    
    // Cards can only be in one place (deck or a player's hand)
    all c: Card | {
        (GameState.deck[m][c] = True) iff (all p: Player | GameState.hands[m][p][c] = False)
    }

    // All cards must be somewhere (deck or player hand)
    all c: Card | {
        GameState.deck[m][c] = True 
        or (one p: Player | GameState.hands[m][p][c] = True)
    }
    
    // Discard pile is empty at start
    all i: Int | no GameState.discard[m][i]
}

// Check if a card can be legally played
pred canPlayCard[m: Move, c: Card] {

    // First card case: Any card can be played if discard pile is empty
    (no i: Int | some GameState.discard[m][i])

    or

    // Normal play case: Card must match top card in some way
    (some topCard: Card | {
        // Find the top card (highest index in discard pile)
        some i: Int | {
            GameState.discard[m][i] = topCard
            // Ensure it's truly the top card
            no j: Int | j > i and some GameState.discard[m][j]
        }
        
        // Legal play conditions:
        // 1. If top card is Wild, new card must match chosen color
        (topCard.value in Wild + WildDrawFour and GameState.chosenColor[m][topCard] = c.color) or
        // 2. Card matches color of top card (for non-wild top cards)
        (topCard.value not in Wild + WildDrawFour and c.color = topCard.color) or
        // 3. Card matches value of top card
        (c.value = topCard.value) or
        // 4. Card is Wild (can be played anytime)
        (c.value in Wild + WildDrawFour)
    })
}

// Draw a card from the deck
pred drawCard[p: Player, m1, m2: Move] {
    some c: Card | {
        // Card must be in deck before drawing
        GameState.deck[m1][c] = True

        // After drawing:
        // Move card from deck to player's hand
        GameState.deck[m2][c] = False
        GameState.hands[m2][p][c] = True
        
        // Other cards remain unchanged
        all otherCard: Card - c | {
            // Deck status preserved for other cards
            GameState.deck[m2][otherCard] = GameState.deck[m1][otherCard]
            // Hand status preserved for other cards
            all otherPlayer: Player | {
                GameState.hands[m2][otherPlayer][otherCard] = GameState.hands[m1][otherPlayer][otherCard]
            }
        }
        
        // Discard pile remains unchanged
        all i: Int | {
            GameState.discard[m2][i] = GameState.discard[m1][i]
        }
    }
}

// Helper predicate to add a card to player's hand
pred addToHand[p: Player, c: Card, m1, m2 : Move]{
    // Move card from deck to player's hand
    GameState.deck[m1][c] = True
    GameState.hands[m2][p][c] = True
    GameState.deck[m2][c] = False
}

// Skip next player's turn (simplified for 2-player game)
pred skipOver[p: Player, skipPlayer: Player, m1, m2: Move]{
    // In 2-player game, skipping means current player gets another turn
    GameState.currentPlayer[m2][p] = True
}                                                         

// Move to next player (simplified for 2-player game)
pred moveNextPlayer[p: Player, m1, m2: Move]{
    m1.next = m2
    // Find other player and make them current
    some other: Player | { 
        other != p 
        GameState.currentPlayer[m2][other] = True
        GameState.currentPlayer[m2][p] = False 
    }
}

// Game ends when a player has no cards left
pred gameOver{
    // No more moves possible after a player runs out of cards
    some m: Move | some p: Player | {
        #{c: Card | GameState.hands[m][p][c] = True} = 0
        no m.next}
}

// Ensure colors are only chosen for wild cards
pred chosenColorForWildOnly {
    all m: Move, c: Card | {
        c.value not in Wild + WildDrawFour implies no GameState.chosenColor[m][c]
    }
}

// Play a card from hand
pred playCard[m1, m2: Move, p: Player, c: Card] {
    m1.next = m2
    // Player must be current player
    GameState.currentPlayer[m1][p] = True
    // Card must be playable per rules
    canPlayCard[m1, c]
    // Card must be in player's hand
    GameState.hands[m1][p][c] = True
    // Remove card from player's hand
    GameState.hands[m2][p][c] = False
    
    // Add card to discard pile at next index
    some i: Int | {
        // Find current highest index
        some GameState.discard[m1][i]
        no j: Int | j > i and some GameState.discard[m1][j]
        
        // Add at next index
        GameState.discard[m2][add[i, 1]] = c
    } or {
        // Handle first card case (empty discard pile)
        (all j: Int | no GameState.discard[m1][j])
        GameState.discard[m2][1] = c
    }

    // Set pending action for special cards
    (c.value in Skip + DrawTwo + Wild + WildDrawFour)
      implies (GameState.pendingAction[m2] = c.value) else {
        no GameState.pendingAction[m2]
    }
 
    // Keep other cards unchanged
    all otherCard: Card - c | {
        // Deck remains the same
        GameState.deck[m1][otherCard] = GameState.deck[m2][otherCard]
        // Player hands remain the same
        all player: Player | {
            GameState.hands[m1][player][otherCard] = GameState.hands[m2][player][otherCard]
        }
    }
    
    // Discard pile unchanged except for new card
    all idx: Int | all discardCard: Card | {
        (GameState.discard[m1][idx] = discardCard and discardCard != c) implies 
            GameState.discard[m2][idx] = discardCard
    }
    
}

// Handle effects of action cards
pred resolveAction[m1, m2: Move, c: Card, p: Player] {
  some val: Value | {
    GameState.pendingAction[m1] = val

    // Dispatch to appropriate action handler
    (val = Skip) implies { some p: Player | skipAction[m1, m2, p] } else
    (val = DrawTwo) implies { some p: Player | drawTwoAction[m1, m2, p] } else
    (val = Wild) implies { some p: Player | wildAction[m1, m2, c, p] } else
    (val = WildDrawFour) implies { some p: Player | wildDrawFourAction[m1, m2, p, c] } 
    
  }
}

// Handle Skip card action
pred skipAction[m1, m2: Move, p: Player] {
    m1.next = m2
    
    // Current player gets another turn (skip next player)
    GameState.currentPlayer[m2][p] = True
    some q: Player | {
        q != p 
        GameState.currentPlayer[m2][q] = False}

    // Clear pending action
    no GameState.pendingAction[m2]
}

// Handle Draw Two card action
pred drawTwoAction[m1, m2: Move, p: Player] {
    m1.next = m2

    some other: Player | { 
        other != p 

        // Other player draws two cards
        some c1, c2: Card | {
            c1 != c2
            addToHand[p, c1, m1, m2]
            addToHand[p, c2, m1, m2]
        }

        // Current player keeps turn
        GameState.currentPlayer[m2][p] = True
        GameState.currentPlayer[m2][other] = False
    }

    // Clear pending action
    no GameState.pendingAction[m2]
}

// Handle Wild card action
pred wildAction[m1, m2: Move, c: Card, p: Player] {
    m1.next = m2
    // Player chooses a color
    some col: Color | {
       GameState.chosenColor[m2][c] = col
    }
    // Move to next player
    moveNextPlayer[p, m1, m2] 
    // Clear pending action
    no GameState.pendingAction[m2]
}

// Handle Wild Draw Four card action
pred wildDrawFourAction[m1, m2: Move, p: Player, c: Card] {
    m1.next = m2

    // Other player draws four cards
    some other: Player | { 
        other != p 
        some c1, c2, c3, c4: Card | {
            // Ensure all cards are different
            c1 != c2 and c1 != c3 and c1 != c4
            c2 != c3 and c2 != c4
            c3 != c4
        
            // Add four cards to other player's hand
            addToHand[p, c1, m1, m2]
            addToHand[p, c2, m1, m2]
            addToHand[p, c3, m1, m2]
            addToHand[p, c4, m1, m2]
        }   
        // Skip other player's turn
        GameState.currentPlayer[m2][p] = True
        GameState.currentPlayer[m2][other] = False
    }
    // Choose new color
    some col: Color | {
       GameState.chosenColor[m2][c] = col
    }

    // Clear pending action
    no GameState.pendingAction[m2]
}

// Player's turn logic
pred playerTurn[m1, m2: Move, p: Player] {
  some c: Card | { 
        // Play a card if possible, otherwise draw
        (GameState.hands[m1][p][c] = True and canPlayCard[m1, c]) implies playCard[m1, m2, p, c] 
        else {drawCard[p, m1, m2]}
    }
}

// Define a short game trace (3 turns)
pred gameTrace {
  chosenColorForWildOnly
  some m0, m1, m2, m3, m4, m5: Move,
       p0, p1: Player,
       c0, c1: Card |
  {
    // Initial setup
    initGame[m0]
    deal[m0]

    // First player's turn
    playerTurn[m0, m1, p0]
    moveNextPlayer[p0, m1, m2]

    // Second player's turn
    playerTurn[m2, m3, p1]
    moveNextPlayer[p1, m3, m4]

    // First player's second turn
    playerTurn[m4, m5, p0]
    gameOver
  }
}

// // Run the short game trace
// run {gameTrace} for exactly 2 Player, exactly 19 Card, 4 Int, exactly 1 GameState, 6 Move for {next is linear}

// Run a more flexible game that focuses on action card effects
run {
  chosenColorForWildOnly
  some m0: Move | {
    initGame[m0]
    deal[m0]
    some m1: Move, p: Player, c: Card | {
      playCard[m0, m1, p, c]
      some m2: Move | {
         // If action card was played, resolve its effect, otherwise move to next player
         (GameState.pendingAction[m1] in (Skip + DrawTwo + Wild + WildDrawFour))
           implies resolveAction[m1, m2, c, p] else moveNextPlayer[p, m1, m2]
      }
    }
  }
  gameOver
} for exactly 2 Player, exactly 19 Card, 4 Int, exactly 1 GameState, 6 Move for {next is linear}

