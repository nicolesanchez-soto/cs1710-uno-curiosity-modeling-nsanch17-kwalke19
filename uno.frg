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

abstract sig Boolean {}
-- Exactly one instance each of True and False
one sig True, False extends Boolean {}

-- Represents state at certain player move
sig Move {
    next: lone Move
}
-- Define the three UNO card colors
abstract sig Color {}
-- Exactly one instance of each color in the game
one sig Red, Blue, Green extends Color {}

-- Define all possible card values in UNO
abstract sig Value {}
-- Number cards from 0-2, exactly one instance of each
one sig Zero, One, Two extends Value {}
-- Action cards - Skip (skip next player),  Draw Two (next player draws 2)
one sig Skip, DrawTwo extends Value {}
-- Wild cards - Wild (change color), Wild Draw Four (change color + next player draws 4)
one sig Wild, WildDrawFour extends Value {}

-- Define card structure
sig Card {
    -- Each card can have at most one color 
    color: lone Color,
    -- Each card must have exactly one value
    value: one Value
}

-- Central game state tracker - exactly one instance to manage the game
one sig GameState {
    -- Track which cards are currently in the deck
    deck: pfunc Move -> Card -> Boolean,
    -- Track order of cards in discard pile using integers
    discard: pfunc Move -> Int -> Card,
    -- Track whose turn it is
    currentPlayer: pfunc Move -> Player -> Boolean,
    -- Track active players in the game
    players: pfunc Move-> Player -> Boolean,
    -- Track which cards are in each player's hand
    hands: pfunc Move -> Player -> Card -> Boolean,
    -- Updated by WildCard color selection
    chosenColor: pfunc Move -> Card -> Color,
    -- Helps track what action is next to reduce overload
    pendingAction: pfunc Move -> Value
}

-- Player representation
sig Player {}

-- Predicate to ensure cards follow UNO rules
pred validCard[c: Card] {
    -- Wild cards start with no color (color chosen when played)
    (c.value in Wild + WildDrawFour) implies no c.color
    -- Non-wild cards must have exactly one color
    (c.value not in Wild + WildDrawFour ) implies some c.color
}

-- Limits the frequency of each card type - reduced the official game for efficiency
pred validCardSpread{
    -- One of each number per color
    all val: Zero + One + Two, c : Color |{
        #{card: Card | card.value = val and card.color = c} = 1
    } 

    -- One of each action type per color
    all v: Skip + DrawTwo, c: Color |
        #{card: Card | card.value = v and card.color = c} = 1 
 
    -- 2 Of each wild card
    #{card: Card | card.value = Wild} = 2
    #{card: Card | card.value = WildDrawFour} = 2

}

-- Initialize a new game state
pred initGame[m0: Move] {
    -- Ensure all cards in play are valid UNO cards
    all c: Card | validCard[c]
    
    -- Discard pile starts empty
    all i: Int, c: Card | no GameState.discard[m0][i]

    -- Set first player (player with position 1) as current
    one p: Player | {
        GameState.currentPlayer[m0][p] = True
    }

    -- Pending action comes from pulling action card
    no GameState.pendingAction[m0]
}

-- Deal initial cards to players
pred deal[m: Move] {
    validCardSpread
    -- Each player should have exactly 7 cards at move m
    all p: Player |
        #{ c: Card | GameState.hands[m][p][c] = True } = 7
    
    -- A card can only be in one place (either deck or one player's hand) at move m
    all c: Card | {
        (GameState.deck[m][c] = True) iff (all p: Player | GameState.hands[m][p][c] = False)
    }

    -- Cards are either in deck or in a player's hand at move m
    all c: Card | {
        GameState.deck[m][c] = True 
        or (one p: Player | GameState.hands[m][p][c] = True)
    }
    -- No cards in the discard pile yet at move m
    all i: Int | no GameState.discard[m][i]
}

-- Predicate to check if a card can be legally played
pred canPlayCard[m: Move, c: Card] {

    -- With no topcard, pick any 
    (no i: Int | some GameState.discard[m][i])

    or

    -- Get the top card of the discard pile (highest index)
    (some topCard: Card | {
        -- Find the highest index in the discard pile
        some i: Int | {
            GameState.discard[m][i] = topCard
            -- Ensure no higher index exists
            no j: Int | j > i and some GameState.discard[m][j]
        }
        
        -- Card can be played if:
        -- Wild and matches chosen color
        (topCard.value in Wild + WildDrawFour and GameState.chosenColor[m][topCard] = c.color) or
        -- It matches the color of the top card (non-wild)
        ( topCard.value not in Wild + WildDrawFour and c.color = topCard.color) or
        -- It matches the value of the top card
        (c.value = topCard.value) or
        -- It's a Wild or Wild Draw Four (can be played anytime)
        (c.value in Wild + WildDrawFour)
    })
}

-- Predicate to draw a card from the deck
pred drawCard[p: Player, m1, m2: Move] {
    some c: Card | {
        -- Card must be in the deck before drawing
        GameState.deck[m1][c] = True

        -- After drawing:
        -- 1. Card is removed from deck
        GameState.deck[m2][c] = False
        -- 2. Card is added to player's hand
        GameState.hands[m2][p][c] = True
        
        -- Only this card moves (all other cards stay where they are)
        all otherCard: Card - c | {
            -- Other cards in deck stay in deck
            GameState.deck[m2][otherCard] = GameState.deck[m1][otherCard]
            -- Other cards in hands stay in their hands
            all otherPlayer: Player | {
                GameState.hands[m2][otherPlayer][otherCard] = GameState.hands[m1][otherPlayer][otherCard]
            }
        }
        
        -- Discard pile remains unchanged
        all i: Int | {
            GameState.discard[m2][i] = GameState.discard[m1][i]
        }
    }
}


pred addToHand[p: Player, c: Card, m1, m2 : Move]{
    -- Remove from deck at next state, add to player hand
    GameState.deck[m1][c] = True
    GameState.hands[m2][p][c] = True
    GameState.deck[m2][c] = False
}

-- defined in terms of 2-person game - person retains turn
pred skipOver[p: Player,skipPlayer: Player, m1, m2: Move]{
    GameState.currentPlayer[m2][p] = True
}                                                         

-- swapping turns for 2 people
pred moveNextPlayer[p: Player, m1, m2: Move]{
    m1.next = m2
    some other: Player | { 
        other != p 
        GameState.currentPlayer[m2][other] = True
        GameState.currentPlayer[m2][p] = False 
    }
}

-- Game ends entirely if a player wins — different from actual game
pred gameOver{
    -- If any player is out of cards, no move can follow
    some m: Move | some p: Player | {
        #{c: Card | GameState.hands[m][p][c] = True} = 0
        no m.next}
}

-- Color only chosen if a wild card
pred chosenColorForWildOnly {
    all m: Move, c: Card | {
        c.value not in Wild + WildDrawFour implies no GameState.chosenColor[m][c]
    }
}

pred playCard[m1, m2: Move, p: Player, c: Card] {
    m1.next = m2
    -- Player must be the current player
    GameState.currentPlayer[m1][p] = True
    -- Card must be legally playable
    canPlayCard[m1, c]
    -- Card must be in player's hand
    GameState.hands[m1][p][c] = True
    -- Remove card from player's hand
    GameState.hands[m2][p][c] = False
    
    -- Find the current top card index and add this card at the next index
    some i: Int | {
        -- Find highest current index in discard pile
        some GameState.discard[m1][i]
        no j: Int | j > i and some GameState.discard[m1][j]
        
        -- Add this card at the next index
        GameState.discard[m2][add[i, 1]] = c
    } or {
        -- Handle the case when discard pile is empty (first card played)
        (all j: Int | no GameState.discard[m1][j])
        GameState.discard[m2][1] = c
    }

    -- Set up pending for later pred if special
    (c.value in Skip + DrawTwo + Wild + WildDrawFour)
      implies (GameState.pendingAction[m2] = c.value) else {
        no GameState.pendingAction[m2]
    }
 
    -- Card locations remain unchanged for all other cards
    all otherCard: Card - c | {
        -- Cards in deck stay in deck
        GameState.deck[m1][otherCard] = GameState.deck[m2][otherCard]
        -- Cards in hands stay in their hands
        all player: Player | {
            GameState.hands[m1][player][otherCard] = GameState.hands[m2][player][otherCard]
        }
    }
    
    -- Positions in discard pile remain unchanged except for the new card
    all idx: Int | all discardCard: Card | {
        (GameState.discard[m1][idx] = discardCard and discardCard != c) implies 
            GameState.discard[m2][idx] = discardCard
    }
    
}

pred resolveAction[m1, m2: Move, c: Card, p: Player] {
  some val: Value | {
    GameState.pendingAction[m1] = val

    (val = Skip) implies { some p: Player | skipAction[m1, m2, p] } else
    (val = DrawTwo) implies { some p: Player | drawTwoAction[m1, m2, p] } else
    (val = Wild) implies { some p: Player | wildAction[m1, m2, c, p] } else
    (val = WildDrawFour) implies { some p: Player | wildDrawFourAction[m1, m2, p, c] } 
    
  }
}

pred skipAction[m1, m2: Move, p: Player] {
    m1.next = m2
    
    -- skip the next player
    GameState.currentPlayer[m2][p] = True
    some q: Player | {
        q != p 
        GameState.currentPlayer[m2][q] = False}

    -- remove pendingAction
    no GameState.pendingAction[m2]
}

pred drawTwoAction[m1, m2: Move, p: Player] {
    m1.next = m2

    some other: Player | { 
        other != p 

    some c1, c2: Card | {
        c1 != c2
        addToHand[p, c1, m1, m2]
        addToHand[p, c2, m1, m2]
    }

    GameState.currentPlayer[m2][p] = True
    GameState.currentPlayer[m2][other] = False}

    no GameState.pendingAction[m2]
}

pred wildAction[m1, m2: Move, c: Card, p: Player] {
    m1.next = m2
    -- Choose a color
    some col: Color | {
       GameState.chosenColor[m2][c] = col
    }
    moveNextPlayer[p, m1, m2] 
    -- Clear pending action
    no GameState.pendingAction[m2]
}

pred wildDrawFourAction[m1, m2: Move, p: Player, c: Card] {
    m1.next = m2

    -- Other player draws
    some other: Player | { 
        other != p 
        some c1, c2, c3, c4: Card | {
            c1 != c2 and c1 != c3 and c1 != c4
            c2 != c3 and c2 != c4
            c3 != c4
        
            addToHand[p, c1, m1, m2]
            addToHand[p, c2, m1, m2]
            addToHand[p, c3, m1, m2]
            addToHand[p, c4, m1, m2]

    }   
    -- Skip other player
        GameState.currentPlayer[m2][p] = True
        GameState.currentPlayer[m2][other] = False
    }
    -- choose color
    some col: Color | {
       GameState.chosenColor[m2][c] = col
    }

    no GameState.pendingAction[m2]
}

pred playerTurn[m1, m2: Move, p: Player] {
  some c: Card | { 
        (GameState.hands[m1][p][c] = True and canPlayCard[m1, c]) implies playCard[m1, m2, p, c] 
        else {drawCard[p, m1, m2]}
    }
}


pred gameTrace {
  chosenColorForWildOnly
  some m0, m1, m2, m3, m4, m5: Move,
       p0, p1: Player,
       c0, c1: Card |
  {
    initGame[m0]
    deal[m0]

    -- Move 1
    playerTurn[m0, m1, p0]
    moveNextPlayer[p0, m1, m2]

    -- Move 2
    playerTurn[m2, m3, p1]
    moveNextPlayer[p1, m3, m4]

    -- Move 3
    playerTurn[m4, m5, p0]
    gameOver
  }
}

run {gameTrace} for exactly 2 Player, exactly 19 Card, 4 Int, exactly 1 GameState, 6 Move for {next is linear}


// run {
//   chosenColorForWildOnly
//   some m0: Move | {
//     initGame[m0]
//     deal[m0]
//     some m1: Move, p: Player, c: Card | {
//       playCard[m0, m1, p, c]
//       some m2: Move | {
//          (GameState.pendingAction[m1] in (Skip + DrawTwo + Wild + WildDrawFour))
//            implies resolveAction[m1, m2, c, p] else moveNextPlayer[p, m1, m2]
//       }
//     }
//   }
//   gameOver
// } for exactly 2 Player, exactly 19 Card, 4 Int, exactly 1 GameState, 6 Move for {next is linear}
