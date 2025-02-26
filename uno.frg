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
-- Define the four UNO card colors
abstract sig Color {}
-- Exactly one instance of each color in the game
one sig Red, Blue, Green extends Color {}

-- Define all possible card values in UNO
abstract sig Value {}
-- Number cards from 0-9, exactly one instance of each
one sig Zero, One, Two extends Value {}
-- Action cards - Skip (skip next player), Reverse (change direction), Draw Two (next player draws 2)
one sig Skip, Reverse, DrawTwo extends Value {}
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
    -- Track game direction (1=clockwise, -1=counterclockwise)
    direction: pfunc Move -> Int -> Boolean,
    -- Track active players in the game
    players: pfunc Move-> Player -> Boolean,
    -- Track which cards are in each player's hand
    hands: pfunc Move -> Player -> Card -> Boolean,
    -- Track player order (each player has a position number)
    playerOrder: pfunc Move -> Player -> Int
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
    all v: Skip + Reverse + DrawTwo, c: Color |
        #{card: Card | card.value = v and card.color = c} = 1
 
    -- 2 Of each wild card
    #{card: Card | card.value = Wild} = 1
    #{card: Card | card.value = WildDrawFour} = 1

}

-- Get the next player in order (considering direction)
pred nextPlayer[current, next: Player, m1, m2: Move] {
    m1.next = m2
    -- Get current player's position
    some pos: Int | {
        GameState.playerOrder[m1][current] = pos 
        -- When direction is clockwise (1)
        (GameState.direction[m1][1] = True) implies {
            -- If at last player, wrap to first
            (pos = #Player) implies {
                GameState.playerOrder[m2][next] = 1
            } else {
                -- Otherwise go to next number
                GameState.playerOrder[m2][next] = add[pos, 1]
            }
        } else {
        -- When direction is counterclockwise (1)
            (pos = 1) implies {
                -- If at first player, wrap to last
                GameState.playerOrder[m2][next] = #Player
            } else {
                -- Otherwise go to prev number
                GameState.playerOrder[m2][next] = subtract[pos, 1]
            }

        }
    }
}

-- Initialize a new game state
pred initGame[m0: Move] {
    -- Set initial game direction to clockwise
    GameState.direction[m0][1] = True
    GameState.direction[m0][-1] = False
    
    -- Ensure all cards in play are valid UNO cards
    all c: Card | validCard[c]
    
    -- Discard pile starts empty
    all i: Int, c: Card | no GameState.discard[m0][i]
    
    -- Each player gets a number from 1 to #Player
    all p: Player | one pos: Int | {
        pos >= 1
        pos <= #Player
        GameState.playerOrder[m0][p] = pos
    }

    -- Assign unique positions to players
    all p1, p2: Player | (p1 != p2) implies (GameState.playerOrder[m0][p1] != GameState.playerOrder[m0][p2])
    
    -- Set first player (player with position 1) as current
    one p: Player | {
        GameState.playerOrder[m0][p] = 1
        GameState.currentPlayer[m0][p] = True
    }
    
    -- UNO requires at least 2 players
    #Player >= 2
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
    -- Get the top card of the discard pile (highest index)
    some topCard: Card | {
        -- Find the highest index in the discard pile
        some i: Int | {
            GameState.discard[m][i] = topCard
            -- Ensure no higher index exists
            no j: Int | j > i and some GameState.discard[m][j]
        }
        
        -- Card can be played if:
        -- 1. It matches the color of the top card
        (c.color = topCard.color) or
        -- 2. It matches the value of the top card
        (c.value = topCard.value) or
        -- 3. It's a Wild or Wild Draw Four (can be played anytime)
        (c.value in Wild + WildDrawFour)
    }
}

-- Predicate to draw a card from the deck
pred drawCard[p: Player, c: Card, m1, m2: Move] {
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
        GameState.discard[m2][i] = GameState.discard[m2][i]
    }

    all pl: Player | {
        GameState.playerOrder[m2][pl] = GameState.playerOrder[m1][pl]
        GameState.currentPlayer[m2][pl] = GameState.currentPlayer[m1][pl]
    }
    all d: Int | {
        GameState.direction[m2][d] = GameState.direction[m1][d]
    }
}

pred addToHand[p: Player, c: Card]{
    GameState.deck[c] = False
    GameState.hands[p][c] = True
}

pred skipOver[p: Player, n: Player, skipPlayer: Player, m1, m2: Move]{
    -- the original player is no longer current and n is skipped
    GameState.currentPlayer[m2][p] = False    
    GameState.currentPlayer[m2][n] = False 
    GameState.currentPlayer[m2][skipPlayer] = True
}

pred moveNextPlayer[p: Player, m1, m2: Move]{
    some n: Player | {
        -- p loses the turn at m2
        GameState.currentPlayer[m2][p] = False
        -- n is the new current player
        GameState.currentPlayer[m2][n] = True
    }
}

pred playCard[m1, m2: Move, p: Player, c: Card] {
    m1.next = m2

    -- Player must be the current player
    GameState.currentPlayer[m1][p] = True
    -- Card must be in player's hand
    GameState.hands[m1][p][c] = True
    -- Card must be legally playable
    // canPlayCard[m1][c]
    
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
    
    -- Remove card from player's hand
    GameState.hands[m2][p][c] = False
    
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
    
    -- Handle special card effects
    one val: Value | c.value = val and {
        -- Skip: Next player's turn is skipped
        (val = Skip) implies {
            some nextPlayer, skipPlayer: Player | {
                skipOver[p, nextPlayer, skipPlayer, m1, m2]
            }
        } else
        -- Reverse: Change game direction
        (val = Reverse) implies {
            -- If currently clockwise (1 = True), switch to counterclockwise
            (GameState.direction[m1][1] = True) implies {
                GameState.direction[m2][1] = False
                GameState.direction[m2][-1] = True
            } else {
                -- If currently counterclockwise (-1 = True), switch to clockwise
                GameState.direction[m2][1] = True
                GameState.direction[m2][-1] = False
            }
            -- Still move to next player (just in new direction)
            moveNextPlayer[p, m1, m2]
        } else
        -- Draw Two: Next player draws 2 cards and is skipped
        (val = DrawTwo) implies {
            some n, skipPlayer: Player | {
                -- Draw 2 cards
                some c1, c2: Card | {
                    c1 != c2
                    -- in the deck at m1
                    GameState.deck[m1][c1] = True
                    GameState.deck[m1][c2] = True

                    -- Remove at m2
                    GameState.deck[m2][c1] = False
                    GameState.deck[m2][c2] = False

                    -- Add to n's hand at m2
                    GameState.hands[m2][n][c1] = True
                    GameState.hands[m2][n][c2] = True
                }
                skipOver[p, n, skipPlayer, m1, m2]
            }
        } else
        -- Wild Draw Four: Next player draws 4 cards and is skipped
        (val = WildDrawFour) implies {
            some n, skipPlayer: Player | {
                -- Draw 4 cards
                some c1, c2, c3, c4: Card | {
                    -- Ensure all cards are different
                    c1 != c2 and c1 != c3 and c1 != c4
                    c2 != c3 and c2 != c4
                    c3 != c4
                    
                    GameState.deck[m1][c1] = True
                    GameState.deck[m1][c2] = True
                    GameState.deck[m1][c3] = True
                    GameState.deck[m1][c4] = True

                    GameState.deck[m2][c1] = False
                    GameState.deck[m2][c2] = False
                    GameState.deck[m2][c3] = False
                    GameState.deck[m2][c4] = False

                    GameState.hands[m2][n][c1] = True
                    GameState.hands[m2][n][c2] = True
                    GameState.hands[m2][n][c3] = True
                    GameState.hands[m2][n][c4] = True
                }
                skipOver[p, n, skipPlayer, m1, m2]   
            }
        } else {
            -- For normal cards and Wild, just move to next player
            moveNextPlayer[p, m1, m2]
        }
    }
}

-- Run command to test initialization, dealing, and player ordering
run {
    -- 1) Choose an initial move m0 (the start state)
    some m0: Move | {
        initGame[m0]        -- sets direction, positions, etc., at m0
        deal[m0]            -- ensures each player has 7 cards at m0
        
        -- 2) Test constraints on the initial state m0
        -- Test that we have proper player ordering
        all p: Player | some pos: Int | {
            pos >= 1
            pos <= #Player
            GameState.playerOrder[m0][p] = pos
        }

        -- Test that we have a current player
        one p: Player | GameState.currentPlayer[m0][p] = True

        -- Test that each player has exactly 7 cards
        all p: Player |
            #{ c: Card | GameState.hands[m0][p][c] = True } = 7


        // all m: Move | {
        //     some p: Player, c: Card | {
        //         playCard[m0, m, p, c]
        //     }
        // }
    }

} for exactly 2 Player, 20 Card, 4 Int, exactly 1 GameState, 3 Move for {next is linear}

-- TODO: wild card adding color
-- TODO: win/loss
-- TODO: losing players