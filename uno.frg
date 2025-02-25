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

-- Define the four UNO card colors
abstract sig Color {}
-- Exactly one instance of each color in the game
one sig Red, Blue, Green, Yellow extends Color {}

-- Define all possible card values in UNO
abstract sig Value {}
-- Number cards from 0-9, exactly one instance of each
one sig Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine extends Value {}
-- Action cards - Skip (skip next player), Reverse (change direction), Draw Two (next player draws 2)
one sig Skip, Reverse, DrawTwo extends Value {}
-- Wild cards - Wild (change color), Wild Draw Four (change color + next player draws 4)
one sig Wild, WildDrawFour extends Value {}

-- Define card structure
sig Card {
    -- Each card can have at most one color (using pfunc for functional relationship)
    color: lone Color,
    -- Each card must have exactly one value
    value: one Value
}

-- Central game state tracker - exactly one instance to manage the game
one sig GameState {
    -- Track which cards are currently in the deck
    deck: pfunc Card -> Boolean,
    -- Track order of cards in discard pile using integers
    discard: pfunc Int -> Card,
    -- Track whose turn it is
    currentPlayer: pfunc Player -> Boolean,
    -- Track game direction (1=clockwise, -1=counterclockwise)
    direction: pfunc Int -> Boolean,
    -- Track active players in the game
    players: pfunc Player -> Boolean,
    -- Track which cards are in each player's hand
    hands: pfunc Player -> Card -> Boolean,
    -- Track player order (each player has a position number)
    playerOrder: pfunc Player -> Int
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

run {
    all c : Card |validCard[c]
} for exactly 4 Player, exactly 10 Card, 4 Int, exactly 1 GameState

-- Get the next player in order (considering direction)
pred nextPlayer[current, next: Player] {
    -- Get current player's position
    some pos: Int | {
        GameState.playerOrder[current] = pos 
        -- When direction is clockwise (1)
        (GameState.direction[1] = True) implies {
            -- If at last player, wrap to first
            (pos = #Player) implies {
                GameState.playerOrder[next] = 1
            } else {
                -- Otherwise go to next number
                GameState.playerOrder[next] = add[pos, 1]
            }
        }
    }
}

-- Initialize a new game state
pred initGame {
    -- Set initial game direction to clockwise
    GameState.direction[1] = True
    GameState.direction[-1] = False
    
    -- Ensure all cards in play are valid UNO cards
    all c: Card | validCard[c]
    
    -- Discard pile starts empty
    all i: Int, c: Card | no GameState.discard[i]
    
    -- Each player gets a unique number from 1 to #Player
    all p: Player | one pos: Int | {
        pos >= 1
        pos <= #Player
        GameState.playerOrder[p] = pos
    }
    
    -- Set first player (player with position 1) as current
    one p: Player | {
        GameState.playerOrder[p] = 1
        GameState.currentPlayer[p] = True
    }
    
    -- UNO requires at least 2 players
    #Player >= 2
}

-- Deal initial cards to players
pred deal {
    -- Each player should have exactly 7 cards
    all p: Player | #{c: Card | GameState.hands[p][c] = True} = 7
    
    -- A card can only be in one place (either deck or one player's hand)
    all c: Card | {
        GameState.deck[c] = True implies (all p: Player | GameState.hands[p][c] = False)
        GameState.deck[c] = False implies (one p: Player | GameState.hands[p][c] = True)
    }
    
    -- Cards are either in deck or in a player's hand
    all c: Card | {
        GameState.deck[c] = True or (one p: Player | GameState.hands[p][c] = True)
    }
    
    -- No cards in discard pile yet
    all i: Int | no GameState.discard[i]
}

-- Predicate to check if a card can be legally played
pred canPlayCard[c: Card] {
    -- Get the top card of the discard pile (highest index)
    some topCard: Card | {
        -- Find the highest index in the discard pile
        some i: Int | {
            GameState.discard[i] = topCard
            -- Ensure no higher index exists
            no j: Int | j > i and some GameState.discard[j]
        }
        
        -- Card can be played if:
        -- 1. It matches the color of the top card
        (some col: Color | {
            c.color = topCard.color
        }) or
        -- 2. It matches the value of the top card
        (some val: Value | {
            c.value = topCard.value
        }) or
        -- 3. It's a Wild or Wild Draw Four (can be played anytime)
        (some val: (Wild + WildDrawFour) | c.value[val] = True)
    }
}

-- Predicate to draw a card from the deck
pred drawCard[p: Player, c: Card] {
    -- Card must be in the deck before drawing
    GameState.deck[c] = True
    
    -- After drawing:
    -- 1. Card is removed from deck
    GameState.deck[c] = False
    -- 2. Card is added to player's hand
    GameState.hands[p][c] = True
    
    -- Only this card moves (all other cards stay where they are)
    all otherCard: Card - c | {
        -- Other cards in deck stay in deck
        GameState.deck[otherCard] = GameState.deck[otherCard]
        -- Other cards in hands stay in their hands
        all otherPlayer: Player | {
            GameState.hands[otherPlayer][otherCard] = GameState.hands[otherPlayer][otherCard]
        }
    }
    
    -- Discard pile remains unchanged
    all i: Int | {
        GameState.discard[i] = GameState.discard[i]
    }
}

pred playCard[p: Player, c: Card] {
    -- Player must be the current player
    GameState.currentPlayer[p] = True
    
    -- Card must be in player's hand
    GameState.hands[p][c] = True
    
    -- Card must be legally playable
    canPlayCard[c]
    
    -- Find the current top card index and add this card at the next index
    some i: Int | {
        -- Find highest current index in discard pile
        some GameState.discard[i]
        no j: Int | j > i and some GameState.discard[j]
        
        -- Add this card at the next index
        GameState.discard[add[i, 1]] = c
    } or {
        -- Handle the case when discard pile is empty (first card played)
        (all j: Int | no GameState.discard[j])
        GameState.discard[1] = c
    }
    
    -- Remove card from player's hand
    GameState.hands[p][c] = False
    
    -- Card locations remain unchanged for all other cards
    all otherCard: Card - c | {
        -- Cards in deck stay in deck
        GameState.deck[otherCard] = GameState.deck[otherCard]
        -- Cards in hands stay in their hands
        all player: Player | {
            GameState.hands[player][otherCard] = GameState.hands[player][otherCard]
        }
    }
    
    -- Positions in discard pile remain unchanged except for the new card
    all idx: Int | all discardCard: Card | {
        (GameState.discard[idx] = discardCard and discardCard != c) implies 
            GameState.discard[idx] = discardCard
    }
    
    -- Handle special card effects
    one val: Value | c.value[val] = True and {
        -- Skip: Next player's turn is skipped
        (val = Skip) implies {
            some nextPlayer, skipPlayer: Player | {
                nextPlayer[p, nextPlayer]
                nextPlayer[nextPlayer, skipPlayer]
                GameState.currentPlayer[p] = False
                GameState.currentPlayer[nextPlayer] = False
                GameState.currentPlayer[skipPlayer] = True
            }
        } else
        -- Reverse: Change game direction
        (val = Reverse) implies {
            -- If currently clockwise (1 = True), switch to counterclockwise
            (GameState.direction[1] = True) implies {
                GameState.direction[1] = False
                GameState.direction[-1] = True
            } else {
                -- If currently counterclockwise (-1 = True), switch to clockwise
                GameState.direction[1] = True
                GameState.direction[-1] = False
            }
            -- Still move to next player (just in new direction)
            some nextPlayer: Player | {
                GameState.currentPlayer[p] = False
                nextPlayer[p, nextPlayer]
                GameState.currentPlayer[nextPlayer] = True
            }
        } else
        -- Draw Two: Next player draws 2 cards and is skipped
        (val = DrawTwo) implies {
            some nextPlayer, skipPlayer: Player | {
                nextPlayer[p, nextPlayer]
                -- Draw 2 cards
                some c1, c2: Card | {
                    c1 != c2
                    GameState.deck[c1] = True
                    GameState.deck[c2] = True
                    GameState.deck[c1] = False
                    GameState.deck[c2] = False
                    GameState.hands[nextPlayer][c1] = True
                    GameState.hands[nextPlayer][c2] = True
                }
                -- Skip their turn
                GameState.currentPlayer[p] = False
                GameState.currentPlayer[nextPlayer] = False
                nextPlayer[nextPlayer, skipPlayer]
                GameState.currentPlayer[skipPlayer] = True
            }
        } else
        -- Wild Draw Four: Next player draws 4 cards and is skipped
        (val = WildDrawFour) implies {
            some nextPlayer, skipPlayer: Player | {
                nextPlayer[p, nextPlayer]
                -- Draw 4 cards
                some c1, c2, c3, c4: Card | {
                    -- Ensure all cards are different
                    c1 != c2 and c1 != c3 and c1 != c4
                    c2 != c3 and c2 != c4
                    c3 != c4
                    
                    -- Take cards from deck
                    GameState.deck[c1] = True
                    GameState.deck[c2] = True
                    GameState.deck[c3] = True
                    GameState.deck[c4] = True
                    
                    -- Move cards to player's hand
                    GameState.deck[c1] = False
                    GameState.deck[c2] = False
                    GameState.deck[c3] = False
                    GameState.deck[c4] = False
                    GameState.hands[nextPlayer][c1] = True
                    GameState.hands[nextPlayer][c2] = True
                    GameState.hands[nextPlayer][c3] = True
                    GameState.hands[nextPlayer][c4] = True
                }
                -- Skip their turn
                GameState.currentPlayer[p] = False
                GameState.currentPlayer[nextPlayer] = False
                nextPlayer[nextPlayer, skipPlayer]
                GameState.currentPlayer[skipPlayer] = True
            }
        } else {
            -- For normal cards and Wild, just move to next player
            some nextPlayer: Player | {
                GameState.currentPlayer[p] = False
                nextPlayer[p, nextPlayer]
                GameState.currentPlayer[nextPlayer] = True
            }
        }
    }
}

-- Run command to test initialization, dealing, and player ordering
// run {
//     initGame
//     deal
    
//     -- Test that we have proper player ordering
//     all p: Player | some pos: Int | {
//         pos >= 1
//         pos <= #Player
//         GameState.playerOrder[p] = pos
//     }
    
//     -- Test that we have a current player
//     one p: Player | GameState.currentPlayer[p] = True
    
//     -- Test that each player has exactly 7 cards
//     all p: Player | #{c: Card | GameState.hands[p][c] = True} = 7

//     -- need to test playCard (been having issues </3)
    
    
// } for exactly 4 Player, exactly 52 Card, 4 Int, exactly 1 GameState