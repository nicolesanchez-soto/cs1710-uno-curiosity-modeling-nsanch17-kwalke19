#lang forge
open "uno.frg"

// Assert relationship between color and value - no underconstraint
pred properColorCard {
    all c: Card | {
        c.value not in (Wild + WildDrawFour)
        some c.color
    }
}

// Players have 7 cards
pred correctHandCount{
    all p: Player | all m: Move |
        #{ c: Card | GameState.hands[m][p][c] = True } = 7
}

// Represents state of cards before/after draw
pred dealCardBehavior {
  all m1, m2: Move, p: Player, c: Card | {
    // After dealing card, hand and deck change but deck should still have same cards as before (except drawn cards)
    GameState.deck[m2][c] = False and GameState.hands[m2][p][c] = True
    all d: Card - c | GameState.deck[m2][d] in GameState.deck[m1][d]
  }
}

// Drawing a card only removes the one card from the deck
pred drawChangesDeck{
    some m1, m2: Move | some c: Card | all oc: Card - c {
        GameState.deck[m2][c] != GameState.deck[m1][c] 
        GameState.deck[m2][oc] = GameState.deck[m1][oc]
    }
}

// Drawing only changes one hand
pred drawChangesOneHand{
    some p: Player | some m1, m2: Move | all c: Card | {
        GameState.hands[m2][p][c] = GameState.hands[m1][p][c] 
    }
}

// Deck not affected by play
pred playRetainsDeck{
    some m1, m2: Move | all c: Card | {
        GameState.deck[m2][c] = GameState.deck[m1][c] 
    }
}

pred initGameWellformed {
  some m0: Move | initGame[m0] implies (
    (no i: Int | some GameState.discard[m0][i])
    and
    (one p: Player | GameState.currentPlayer[m0][p] = True)
    and
    (no GameState.pendingAction[m0])
  )
}

// Verify correct number of colors and values per category
pred properNumberSpread {
    #{c: Card | c.color = Red} = 5
    #{c: Card | c.color = Green} = 5
    #{c: Card | c.color = Blue} = 5

    #{c: Card | c.value = Wild} = 2
    #{c: Card | c.value = WildDrawFour} = 2

    #{c: Card | c.value = Skip} = 3
    #{c: Card | c.value = DrawTwo} = 3

    #{c: Card | c.value = Zero} = 3
    #{c: Card | c.value = One} = 3
    #{c: Card | c.value = Two} = 3
}

test suite for validCard {
    // Good regular card
    example validRegularCard is  {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red
    }
    // Good wild card
     example validWildCard is  {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild
        no `c0.color
    }
    // bad wild card (has color)
     example badWildCard is not {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wdf
        `c0.color = `red
    }
    
    // Bad regular card: either no color or no value
    example badRegularNoColor is not  {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        no `c0.color
    }

    example badRegularNoValue is not {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.color = `red
    }

    assert all c: Card | { properColorCard }  is sufficient for validCard[c]

}

test suite for validCardSpread {
    assert properNumberSpread is necessary for validCardSpread
}

test suite for initGame {
    -- proper game start all cards valid, discard empty, one current, no pending
     example validStart is {all m: Move | initGame[m]} and {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

        no `gs.discard
        `gs.currentPlayer = (`m0, `p0) -> `True
        no `gs.pendingAction
    }

     -- improper game start, creates current action before player picks wild card
     example badStartPendingAction is not {all m: Move | initGame[m]} and {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

        no `gs.discard
        `gs.currentPlayer = (`m0, `p0) -> `True
        `gs.pendingAction = (`m0) -> `wild  // player didn't pick wild card
    }

    // No current player
    example badStartNoPlayer is not {all m: Move | initGame[m]} and {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

        no `gs.discard
        `gs.currentPlayer = (`m0, `p0) -> `False
        no `gs.pendingAction
    }

    // Game shouldn't start with any discarded cards
    example badStartDiscarded is not {all m: Move | initGame[m]} and {all c: Card | validCard[c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.discard = (`m0, 0) -> `c0
        `gs.currentPlayer = (`m0, `p0) -> `True
        no `gs.pendingAction
    }

    assert all m: Move | { initGameWellformed } is necessary for initGame[m]
}

test suite for deal {
    example improperDeal is not {all m: Move | deal[m]} for {
        // Player has 7 cards but not a valid spread - must have cards for each category
        Card = `c0 + `c1 + `c2 + `c3 + `c4 + `c5 + `c6 
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.hands = (`m0,`p0,`c0) -> True + (`m0,`p0,`c1) -> True + (`m0,`p0,`c2) -> True 
                    + (`m0,`p0,`c3) -> True + (`m0,`p0,`c4) -> True
                    + (`m0,`p0,`c5) -> True + (`m0,`p0,`c6) -> True
        `gs.deck = (`m0,`c0) -> False + (`m0,`c1) -> False + (`m0,`c2) -> False 
                    + (`m0,`c3) -> False + (`m0,`c4) -> False
                    + (`m0,`c5) -> False + (`m0,`c6) -> False
    }
    assert dealCardBehavior is sat
    assert all m: Move | {correctHandCount} is necessary for deal[m]
}

test suite for canPlayCard{
    // Card can be played - game hasnt started
    example validFirstPlay is {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0

        Boolean = `True + `False
        True = `True
        False = `False

    
        no `gs.discard
    }
    // Card can be played - color matches
    example canPlayColor is {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red
        `c1.value = `onee
        `c1.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
    
        `gs.discard = (`m0, 0) -> `c0
    }
    
    // Card can be played - color matches chosenColor from wild card
    example canPlayWildColor is {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        `c1.value = `onee
        `c1.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.chosenColor = (`m0, `c0) -> `red
        `gs.discard = (`m0, 0) -> `c0
    } 

    // Card can be played - value matches
    example canPlayValue is {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `onee
        `c0.color = `red
        `c1.value = `onee
        `c1.color = `green

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
    
        `gs.discard = (`m0, 0) -> `c0
    }

    // Card cannot be played - wrong color and value
     example cantPlayNoMatch is not {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `two
        `c0.color = `blue

        `c1.value = `onee
        `c1.color = `green

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.discard = (`m0, 0) -> `c0
    } 

    // Card cannot be played - wrong color and value for wild card
    example cantPlayWildColor is not {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        `c1.value = `onee
        `c1.color = `green

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.chosenColor = (`m0, `c0) -> `red
        `gs.discard = (`m0, 0) -> `c0
    } 

    // Can play wild card after wild card
    example canPlayDoubleWild is {  all c: Card | all m: Move| canPlayCard[m, c]} for {
        Card = `c0 + `c1
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        `c1.value = `wild

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.chosenColor = (`m0, `c0) -> `red
        `gs.discard = (`m0, 0) -> `c0
    } 
}

test suite for drawCard {
    -- example of state change
    example standardDraw is { some m1, m2: Move| all p : Player|drawCard[p, m1, m2]} for {
        Card = `c0 + `c1 + `c2
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild
        `c1.value = `wild
        `c2.value = `wdf

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Setup: In move m0, assign c0 to be in the deck
        `gs.deck = (`m0,`c0) -> True + (`m0,`c1) -> True + (`m1,`c0) -> False + (`m1,`c1) -> True 
        // Ensure no cards are in hands at m0
        `gs.hands = (`m0, `p0, `c0) -> False + (`m0, `p0, `c1) -> False + (`m1, `p0, `c0) -> True + (`m1, `p0, `c1) -> False
        
        `gs.discard = (`m0, 0) -> `c2 + (`m1, 0) -> `c2 
    } 
    
    // Bad example where stays in deck after
    example drawKeepsDeck is not { all m1, m2: Move| all p : Player|drawCard[p, m1, m2]} for {
        Card = `c0 + `c1 + `c2
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild
        `c1.value = `wild
        `c2.value = `wdf

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Setup: In move m0, assign c0 to be in the deck
        `gs.deck = (`m0,`c0) -> True + (`m0,`c1) -> True + (`m1,`c0) -> False + (`m1,`c1) -> True 
        // Ensure no cards are in hands at m0
        `gs.hands = (`m0, `p0, `c0) -> False + (`m0, `p0, `c1) -> False + (`m1, `p0, `c0) -> True + (`m1, `p0, `c1) -> False
        
        `gs.discard = (`m0, 0) -> `c2 + (`m1, 0) -> `c2 
    } 

    assert all p: Player, m1, m2: Move | {drawChangesDeck} is necessary for drawCard[p, m1, m2]
    assert all p: Player, m1, m2: Move | {drawChangesOneHand} is necessary for drawCard[p, m1, m2]
}

test suite for playCard {
    // all conditions correct
    example goodPlayCard is {some m1, m2: Move | all p: Player | all c: Card | playCard[m1, m2, p, c]} for{
        Card = `c0 
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.currentPlayer = (`m0, `p0) -> True
        `gs.deck = (`m0, `c0) -> False + (`m1, `c0) -> False
        `gs.hands = (`m0,`p0, `c0) -> True + (`m1, `p0, `c0) -> False
        `gs.pendingAction = (`m1) -> `wild
    }

    // Wrong: card still in hand
    example keepHandInPlayCard is not {some m1, m2: Move | all p: Player | all c: Card | playCard[m1, m2, p, c]} for{
        Card = `c0 
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.currentPlayer = (`m0, `p0) -> True
        `gs.deck = (`m0, `c0) -> False + (`m1, `c0) -> False
        `gs.hands = (`m0,`p0, `c0) -> True + (`m1, `p0, `c0) -> True
        `gs.pendingAction = (`m1) -> `wild
    }

    // Wrong: no pending action from playing special card
    example pendingNotUpdated is not {some m1, m2: Move | all p: Player | all c: Card | playCard[m1, m2, p, c]} for{
        Card = `c0 
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `wild

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        `gs.currentPlayer = (`m0, `p0) -> True
        `gs.deck = (`m0, `c0) -> False + (`m1, `c0) -> False
        `gs.hands = (`m0,`p0, `c0) -> True + (`m1, `p0, `c0) -> True
        no `gs.pendingAction
    }

    assert all m1, m2: Move, p: Player, c: Card | {playRetainsDeck} is necessary for playCard[m1,m2,p,c]
}

test suite for addToHand {
    // Successful card addition
    example validAddToHand is {some m1, m2: Move | some p: Player | some c: Card | addToHand[p, c, m1, m2]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Card is in the deck in move m0
        `gs.deck = (`m0, `c0) -> True + (`m1, `c0) -> False
        // Card is not in player's hand in m0 but is in m1
        `gs.hands = (`m0, `p0, `c0) -> False + (`m1, `p0, `c0) -> True
    }

    // Invalid case - card wasn't in deck initially
    example cardNotInDeck is not {some m1, m2: Move | some p: Player | some c: Card | addToHand[p, c, m1, m2]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Card is NOT in the deck in move m0
        `gs.deck = (`m0, `c0) -> False + (`m1, `c0) -> False
        // Card is in player's hand in m1
        `gs.hands = (`m0, `p0, `c0) -> False + (`m1, `p0, `c0) -> True
    }

    // Invalid case - card stays in deck after adding to hand
    example cardStaysInDeck is not {some m1, m2: Move | some p: Player | some c: Card | addToHand[p, c, m1, m2]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Card is in the deck in both moves (should be removed in m1)
        `gs.deck = (`m0, `c0) -> True + (`m1, `c0) -> True
        // Card is added to player's hand
        `gs.hands = (`m0, `p0, `c0) -> False + (`m1, `p0, `c0) -> True
    }

    // Invalid case - card not added to player's hand
    example cardNotAddedToHand is not {some m1, m2: Move | some p: Player | some c: Card | addToHand[p, c, m1, m2]} for {
        Card = `c0
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        `c0.value = `zero
        `c0.color = `red

        Player = `p0
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Card is in the deck in m0 and removed in m1
        `gs.deck = (`m0, `c0) -> True + (`m1, `c0) -> False
        // Card is not added to player's hand in m1
        `gs.hands = (`m0, `p0, `c0) -> False + (`m1, `p0, `c0) -> False
    }
}
test suite for moveNextPlayer {
    // Valid move to next player in 2-player game
    example validNextPlayer is {some m1, m2: Move | some p: Player | moveNextPlayer[p, m1, m2]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Set current player state directly
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False + 
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        // m0 points to m1 as next move
        `m0.next = `m1
    }

    // Invalid - no current player after move
    example invalidNoCurrentPlayer is not {some m1, m2: Move | some p: Player | moveNextPlayer[p, m1, m2]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // No current player after move
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False + 
                          (`m1, `p0) -> False + (`m1, `p1) -> False
        // m0 points to m1 as next move
        `m0.next = `m1
    }

    // Invalid - multiple current players after move
    example invalidMultipleCurrentPlayers is not {some m1, m2: Move | some p: Player | moveNextPlayer[p, m1, m2]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Multiple current players after move
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False + 
                          (`m1, `p0) -> True + (`m1, `p1) -> True
        // m0 points to m1 as next move
        `m0.next = `m1
    }
}

test suite for skipOver {
    // Valid skip - current player gets another turn
    example validSkip is {some m1, m2: Move | some p, skipPlayer: Player | skipOver[p, skipPlayer, m1, m2]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False

        // Define all currentPlayer mappings in one statement
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False + 
                          (`m1, `p0) -> True + (`m1, `p1) -> False
    }
}
test suite for gameOver {
    // Valid game over - player has no cards left and no next move
    example validGameOver is {gameOver} for {
        Player = `p0 + `p1
        Card = `c0 + `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Player p0 has 0 cards in final move m1
        `gs.hands = (`m0, `p0, `c0) -> True + (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m0, `p1, `c0) -> False + (`m0, `p1, `c1) -> True + (`m0, `p1, `c2) -> True +
                  (`m1, `p0, `c0) -> False + (`m1, `p0, `c1) -> False + (`m1, `p0, `c2) -> False +
                  (`m1, `p1, `c0) -> False + (`m1, `p1, `c1) -> True + (`m1, `p1, `c2) -> True
        
        // No next move after m1
        `m0.next = `m1
        no `m1.next
    }
    
    // Invalid - player has no cards but game continues (has next move)
    example invalidGameContinues is not {gameOver} for {
        Player = `p0 + `p1
        Card = `c0 + `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1 + `m2

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Player p0 has 0 cards in move m1
        `gs.hands = (`m0, `p0, `c0) -> True + (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m0, `p1, `c0) -> False + (`m0, `p1, `c1) -> True + (`m0, `p1, `c2) -> True +
                  (`m1, `p0, `c0) -> False + (`m1, `p0, `c1) -> False + (`m1, `p0, `c2) -> False +
                  (`m1, `p1, `c0) -> False + (`m1, `p1, `c1) -> True + (`m1, `p1, `c2) -> True
        
        // Game continues (has next move) even though player has no cards
        `m0.next = `m1
        `m1.next = `m2
    }
    
    // Invalid - no player has empty hand, but no next move
    example invalidNoEmptyHandButEnds is not {gameOver} for {
        Player = `p0 + `p1
        Card = `c0 + `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // No player has 0 cards
        `gs.hands = (`m0, `p0, `c0) -> True + (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m0, `p1, `c0) -> False + (`m0, `p1, `c1) -> True + (`m0, `p1, `c2) -> True +
                  (`m1, `p0, `c0) -> True + (`m1, `p0, `c1) -> False + (`m1, `p0, `c2) -> False +
                  (`m1, `p1, `c0) -> False + (`m1, `p1, `c1) -> True + (`m1, `p1, `c2) -> True
        
        // No next move after m1
        `m0.next = `m1
        no `m1.next
    }
}

test suite for chosenColorForWildOnly {
    // Valid case - only wild cards have chosen colors
    example validChosenColorForWildOnly is {chosenColorForWildOnly} for {
        Card = `wildCard + `regularCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0
        
        // Define card types
        `wildCard.value = `wild
        no `wildCard.color
        `regularCard.value = `zero
        `regularCard.color = `red
        
        // Only wild card has chosen color
        `gs.chosenColor = (`m0, `wildCard) -> `blue
    }
    
    // Invalid case - regular card has chosen color
    example invalidRegularCardWithChosenColor is not {chosenColorForWildOnly} for {
        Card = `wildCard + `regularCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0
        
        // Define card types
        `wildCard.value = `wild
        no `wildCard.color
        `regularCard.value = `zero
        `regularCard.color = `red
        
        // Both wild and regular card have chosen colors (invalid)
        `gs.chosenColor = (`m0, `wildCard) -> `blue + (`m0, `regularCard) -> `green
    }
    
    // Valid case - wild draw four has chosen color
    example validWildDrawFourChosenColor is {chosenColorForWildOnly} for {
        Card = `wildDrawFourCard + `regularCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0
        
        // Define card types
        `wildDrawFourCard.value = `wdf
        no `wildDrawFourCard.color
        `regularCard.value = `zero
        `regularCard.color = `red
        
        // Only WildDrawFour card has chosen color
        `gs.chosenColor = (`m0, `wildDrawFourCard) -> `blue
    }
    
    // Invalid case - action card has chosen color
    example invalidActionCardWithChosenColor is not {chosenColorForWildOnly} for {
        Card = `wildCard + `skipCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0
        
        // Define card types
        `wildCard.value = `wild
        no `wildCard.color
        `skipCard.value = `skip
        `skipCard.color = `red
        
        // Both wild and action cards have chosen colors (invalid)
        `gs.chosenColor = (`m0, `wildCard) -> `blue + (`m0, `skipCard) -> `green
    }
}

test suite for wildAction {
    // Valid Wild action - color is chosen and moves to next player
    example validWildAction is {some m1, m2: Move | some c: Card | some p: Player | wildAction[m1, m2, c, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1
        Card = `wildCard

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define wild card
        `wildCard.value = `wild
        no `wildCard.color
        
        // Wild card has chosen color
        `gs.chosenColor = (`m1, `wildCard) -> `blue
        
        // Current player changes after Wild
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wild
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - no color chosen after Wild
    example invalidWildNoColorChosen is not {some m1, m2: Move | some c: Card | some p: Player | wildAction[m1, m2, c, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1
        Card = `wildCard

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define wild card
        `wildCard.value = `wild
        no `wildCard.color
        
        // No color chosen (invalid)
        no `gs.chosenColor
        
        // Current player changes after Wild
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wild
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - pending action not cleared after Wild
    example invalidWildPendingActionRemains is not {some m1, m2: Move | some c: Card | some p: Player | wildAction[m1, m2, c, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1
        Card = `wildCard

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define wild card
        `wildCard.value = `wild
        no `wildCard.color
        
        // Wild card has chosen color
        `gs.chosenColor = (`m1, `wildCard) -> `blue
        
        // Current player changes after Wild
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Pending action not cleared (invalid)
        `gs.pendingAction = `m0 -> `wild + `m1 -> `wild
        
        // Moves are linked
        `m0.next = `m1
    }
}


// Wild cards cannot have a predefined color
pred wildCardsNoColor {
    all c: Card | (c.value in Wild + WildDrawFour) implies no c.color
}

// Non-wild cards must have exactly one color
pred nonWildCardsHaveColor {
    all c: Card | (c.value not in Wild + WildDrawFour) implies one c.color
}

// Test that validCard is composed of these two rules
test suite for validCard {
    assert all c: Card | { wildCardsNoColor and nonWildCardsHaveColor } is sufficient for validCard[c]
}


// Chosen colors can only be assigned to wild cards
pred onlyWildCardsHaveChosenColor {
    all m: Move, c: Card | c.value not in Wild + WildDrawFour implies 
        no GameState.chosenColor[m][c]
}


// Test that chosen colors follow the rules
test suite for chosenColorForWildOnly {
    assert { onlyWildCardsHaveChosenColor } is sufficient for chosenColorForWildOnly
}


test suite for wildDrawFourAction {
    // Valid Wild Draw Four action - player draws four cards, color is chosen, current player keeps turn
    example validWildDrawFourAction is {some m1, m2: Move | some p: Player | some c: Card | wildDrawFourAction[m1, m2, p, c]} for {
        Player = `p0 + `p1
        Card = `wdfCard + `c1 + `c2 + `c3 + `c4
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define the Wild Draw Four card
        `wdfCard.value = `wdf
        no `wdfCard.color
        
        // Color is chosen for the Wild Draw Four card
        `gs.chosenColor = (`m1, `wdfCard) -> `blue
        
        // Four cards are in deck initially, then moved to player's hand
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True + (`m0, `c3) -> True + (`m0, `c4) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False + (`m1, `c3) -> False + (`m1, `c4) -> False
        
        // Four cards are added to player's hand
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False + 
                  (`m0, `p0, `c3) -> False + (`m0, `p0, `c4) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True + 
                  (`m1, `p0, `c3) -> True + (`m1, `p0, `c4) -> True
        
        // Current player state - p0 stays current after Wild Draw Four
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wdf
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - no color chosen after Wild Draw Four
    example invalidWDFNoColorChosen is not {some m1, m2: Move | some p: Player | some c: Card | wildDrawFourAction[m1, m2, p, c]} for {
        Player = `p0 + `p1
        Card = `wdfCard + `c1 + `c2 + `c3 + `c4
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define the Wild Draw Four card
        `wdfCard.value = `wdf
        no `wdfCard.color
        
        // No color chosen (invalid)
        no `gs.chosenColor
        
        // Four cards drawn correctly
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True + (`m0, `c3) -> True + (`m0, `c4) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False + (`m1, `c3) -> False + (`m1, `c4) -> False
        
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False + 
                  (`m0, `p0, `c3) -> False + (`m0, `p0, `c4) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True + 
                  (`m1, `p0, `c3) -> True + (`m1, `p0, `c4) -> True
        
        // Current player stays the same
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wdf
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - fewer than four cards drawn
    example invalidWDFFewerCardsDraw is not {some m1, m2: Move | some p: Player | some c: Card | wildDrawFourAction[m1, m2, p, c]} for {
        Player = `p0 + `p1
        Card = `wdfCard + `c1 + `c2 + `c3
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define the Wild Draw Four card
        `wdfCard.value = `wdf
        no `wdfCard.color
        
        // Color is chosen
        `gs.chosenColor = (`m1, `wdfCard) -> `blue
        
        // Only three cards drawn (invalid)
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True + (`m0, `c3) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False + (`m1, `c3) -> False
        
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False + (`m0, `p0, `c3) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True + (`m1, `p0, `c3) -> True
        
        // Current player stays the same
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wdf
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - current player doesn't keep turn
    example invalidWDFPlayerDoesntKeepTurn is not {some m1, m2: Move | some p: Player | some c: Card | wildDrawFourAction[m1, m2, p, c]} for {
        Player = `p0 + `p1
        Card = `wdfCard + `c1 + `c2 + `c3 + `c4
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define the Wild Draw Four card
        `wdfCard.value = `wdf
        no `wdfCard.color
        
        // Color is chosen
        `gs.chosenColor = (`m1, `wdfCard) -> `blue
        
        // Four cards drawn correctly
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True + (`m0, `c3) -> True + (`m0, `c4) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False + (`m1, `c3) -> False + (`m1, `c4) -> False
        
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False + 
                  (`m0, `p0, `c3) -> False + (`m0, `p0, `c4) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True + 
                  (`m1, `p0, `c3) -> True + (`m1, `p0, `c4) -> True
        
        // Current player changes (invalid)
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wdf
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - pending action not cleared
    example invalidWDFPendingActionRemains is not {some m1, m2: Move | some p: Player | some c: Card | wildDrawFourAction[m1, m2, p, c]} for {
        Player = `p0 + `p1
        Card = `wdfCard + `c1 + `c2 + `c3 + `c4
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define the Wild Draw Four card
        `wdfCard.value = `wdf
        no `wdfCard.color
        
        // Color is chosen
        `gs.chosenColor = (`m1, `wdfCard) -> `blue
        
        // Four cards drawn correctly
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True + (`m0, `c3) -> True + (`m0, `c4) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False + (`m1, `c3) -> False + (`m1, `c4) -> False
        
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False + 
                  (`m0, `p0, `c3) -> False + (`m0, `p0, `c4) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True + 
                  (`m1, `p0, `c3) -> True + (`m1, `p0, `c4) -> True
        
        // Current player stays the same
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Pending action not cleared (invalid)
        `gs.pendingAction = `m0 -> `wdf + `m1 -> `wdf
        
        // Moves are linked
        `m0.next = `m1
    }
}

test suite for drawTwoAction {
    // Valid Draw Two action - other player draws two cards and current player keeps turn
    example validDrawTwoAction is {some m1, m2: Move | some p: Player | drawTwoAction[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Cards are in deck initially, then moved to player's hand
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False
        
        // Two cards are added to player's hand
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True
        
        // Current player state - p0 stays current after Draw Two
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `drawtwo
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - fewer than two cards drawn
    example invalidFewerCardsDraw is not {some m1, m2: Move | some p: Player | drawTwoAction[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Only one card drawn (invalid)
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> True
        
        // Only one card added to player's hand
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> False
        
        // Current player state correct
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `drawtwo
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - current player doesn't keep turn
    example invalidPlayerDoesntKeepTurn is not {some m1, m2: Move | some p: Player | drawTwoAction[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Two cards drawn correctly
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False
        
        // Two cards added to player's hand
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True
        
        // Current player changes (invalid)
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `drawtwo
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - pending action not cleared
    example invalidPendingActionRemains is not {some m1, m2: Move | some p: Player | drawTwoAction[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Two cards drawn correctly
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False
        
        // Two cards added to player's hand
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m1, `p0, `c1) -> True + (`m1, `p0, `c2) -> True
        
        // Current player state correct
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Pending action not cleared (invalid)
        `gs.pendingAction = `m0 -> `drawtwo + `m1 -> `drawtwo
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - cards not added to player's hand
    example invalidCardsNotAddedToHand is not {some m1, m2: Move | some p: Player | drawTwoAction[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Two cards removed from deck
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> True +
                 (`m1, `c1) -> False + (`m1, `c2) -> False
        
        // Cards not added to player's hand (invalid)
        `gs.hands = (`m0, `p0, `c1) -> False + (`m0, `p0, `c2) -> False +
                  (`m1, `p0, `c1) -> False + (`m1, `p0, `c2) -> False
        
        // Current player state correct
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `drawtwo
        
        // Moves are linked
        `m0.next = `m1
    }
}

test suite for resolveAction {
    // Valid resolution of Skip action
    example validResolveSkipAction is {some m1, m2: Move | some c: Card | some p: Player | resolveAction[m1, m2, c, p]} for {
        Card = `skipCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0 + `m1
        Player = `p0 + `p1
        
        Boolean = `True + `False
        True = `True
        False = `False
        
        // Define skip card
        `skipCard.value = `skip
        `skipCard.color = `red
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `skip
        
        // Current player state (p0 stays current after Skip)
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Valid resolution of Wild action
    example validResolveWildAction is {some m1, m2: Move | some c: Card | some p: Player | resolveAction[m1, m2, c, p]} for {
        Card = `wildCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0 + `m1
        Player = `p0 + `p1
        
        Boolean = `True + `False
        True = `True
        False = `False
        
        // Define wild card
        `wildCard.value = `wild
        no `wildCard.color
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wild
        
        // Wild card has chosen color
        `gs.chosenColor = (`m1, `wildCard) -> `blue
        
        // Current player changes after Wild
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> False + (`m1, `p1) -> True
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Valid resolution of Draw Two action
    example validResolveDrawTwoAction is {some m1, m2: Move | some c: Card | some p: Player | resolveAction[m1, m2, c, p]} for {
        Card = `drawTwoCard + `card1 + `card2
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0 + `m1
        Player = `p0 + `p1
        
        Boolean = `True + `False
        True = `True
        False = `False
        
        // Define cards
        `drawTwoCard.value = `drawtwo
        `drawTwoCard.color = `red
        `card1.value = `zero
        `card1.color = `blue
        `card2.value = `onee
        `card2.color = `green
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `drawtwo
        
        // Current player state (p0 stays current after Draw Two)
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Cards are drawn from deck to player's hand
        `gs.deck = (`m0, `card1) -> True + (`m0, `card2) -> True +
                 (`m1, `card1) -> False + (`m1, `card2) -> False
        
        `gs.hands = (`m0, `p0, `card1) -> False + (`m0, `p0, `card2) -> False +
                  (`m1, `p0, `card1) -> True + (`m1, `p0, `card2) -> True
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Valid resolution of Wild Draw Four action
    example validResolveWildDrawFourAction is {some m1, m2: Move | some c: Card | some p: Player | resolveAction[m1, m2, c, p]} for {
        Card = `wildDrawFourCard + `card1 + `card2 + `card3 + `card4
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0 + `m1
        Player = `p0 + `p1
        
        Boolean = `True + `False
        True = `True
        False = `False
        
        // Define cards
        `wildDrawFourCard.value = `wdf
        no `wildDrawFourCard.color
        `card1.value = `zero
        `card1.color = `blue
        `card2.value = `onee
        `card2.color = `green
        `card3.value = `two
        `card3.color = `red
        `card4.value = `skip
        `card4.color = `blue
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `wdf
        
        // Wild card has chosen color
        `gs.chosenColor = (`m1, `wildDrawFourCard) -> `blue
        
        // Current player state (p0 stays current after WDF)
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Cards are drawn from deck to player's hand
        `gs.deck = (`m0, `card1) -> True + (`m0, `card2) -> True + (`m0, `card3) -> True + (`m0, `card4) -> True +
                 (`m1, `card1) -> False + (`m1, `card2) -> False + (`m1, `card3) -> False + (`m1, `card4) -> False
        
        `gs.hands = (`m0, `p0, `card1) -> False + (`m0, `p0, `card2) -> False + 
                  (`m0, `p0, `card3) -> False + (`m0, `p0, `card4) -> False +
                  (`m1, `p0, `card1) -> True + (`m1, `p0, `card2) -> True + 
                  (`m1, `p0, `card3) -> True + (`m1, `p0, `card4) -> True
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - no pending action to resolve
    example invalidResolveNoPendingAction is not {some m1, m2: Move | some c: Card | some p: Player | resolveAction[m1, m2, c, p]} for {
        Card = `skipCard
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        GameState = `gs
        Move = `m0 + `m1
        Player = `p0 + `p1
        
        Boolean = `True + `False
        True = `True
        False = `False
        
        // Define skip card
        `skipCard.value = `skip
        `skipCard.color = `red
        
        // No pending action to resolve (invalid)
        no `gs.pendingAction
        
        // Current player state
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Moves are linked
        `m0.next = `m1
    }
}

test suite for skipAction {
    // Valid Skip action - current player gets another turn
    example validSkipAction is {some m1, m2: Move | some p: Player | skipAction[m1, m2, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Current player state - p0 stays current after Skip
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `skip
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - pending action not cleared
    example invalidSkipPendingActionRemains is not {some m1, m2: Move | some p: Player | skipAction[m1, m2, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Current player state is correct
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Pending action not cleared (invalid)
        `gs.pendingAction = `m0 -> `skip + `m1 -> `skip
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - next move relationship not established
    example invalidSkipNextNotEstablished is not {some m1, m2: Move | some p: Player | skipAction[m1, m2, p]} for {
        Player = `p0 + `p1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Current player state is correct
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False +
                          (`m1, `p0) -> True + (`m1, `p1) -> False
        
        // Set up pending action in m0 only
        `gs.pendingAction = `m0 -> `skip
        
        // Next move relationship not established (invalid)
        no `m0.next
    }
}test suite for playerTurn {
    
    // Valid player turn - player has no playable cards and draws
    example validPlayerDrawsCard is {some m1, m2: Move | some p: Player | playerTurn[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c0 + `c1 + `c2
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define cards
        `c0.value = `zero
        `c0.color = `red
        `c1.value = `onee
        `c1.color = `blue
        `c2.value = `two
        `c2.color = `green
        
        // Player has cards that can't be played
        `gs.hands = (`m0, `p0, `c0) -> True + (`m0, `p0, `c1) -> False +
                  (`m1, `p0, `c0) -> True + (`m1, `p0, `c1) -> True
        
        // Card c1 is in deck initially, drawn by player
        `gs.deck = (`m0, `c1) -> True + (`m0, `c2) -> False +
                 (`m1, `c1) -> False + (`m1, `c2) -> False
        
        // Current player
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False
        
        // Top discard card that doesn't match player's cards
        `gs.discard = (`m0, 0) -> `c2 + (`m1, 0) -> `c2
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - player plays a card they can't play
    example invalidPlaysInvalidCard is not {some m1, m2: Move | some p: Player | playerTurn[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c0 + `c1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define cards with different colors and values
        `c0.value = `zero
        `c0.color = `red
        `c1.value = `onee
        `c1.color = `blue
        
        // Player has card in hand and tries to play it (though it doesn't match)
        `gs.hands = (`m0, `p0, `c1) -> True +
                  (`m1, `p0, `c1) -> False
        
        // Current player
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False
        
        // Top discard card doesn't match player's card in color or value
        `gs.discard = (`m0, 0) -> `c0 + (`m1, 1) -> `c1
        
        // Moves are linked
        `m0.next = `m1
    }
    
    // Invalid - no action taken (neither plays nor draws)
    example invalidNoAction is not {some m1, m2: Move | some p: Player | playerTurn[m1, m2, p]} for {
        Player = `p0 + `p1
        Card = `c0 + `c1
        GameState = `gs
        Move = `m0 + `m1

        Boolean = `True + `False
        True = `True
        False = `False
        
        Color = `blue + `green + `red
        Value = `zero + `onee + `two + `skip + `drawtwo + `wild + `wdf
        Zero = `zero
        One = `onee
        Two = `two
        Blue = `blue
        Green = `green
        Red = `red
        Skip = `skip
        DrawTwo = `drawtwo
        Wild = `wild
        WildDrawFour = `wdf
        
        // Define cards - different colors and values
        `c0.value = `zero
        `c0.color = `red
        `c1.value = `onee
        `c1.color = `blue
        
        // Hand remains the same (no card played)
        `gs.hands = (`m0, `p0, `c1) -> True +
                  (`m1, `p0, `c1) -> True
        
        // Deck remains the same (no card drawn)
        `gs.deck = (`m0, `c0) -> True +
                 (`m1, `c0) -> True
        
        // Current player
        `gs.currentPlayer = (`m0, `p0) -> True + (`m0, `p1) -> False
        
        // Discard pile remains the same
        no `gs.discard
        
        // Moves are linked
        `m0.next = `m1
    }
}

// When playing a card, it's removed from hand and added to discard
pred playCardMovesToDiscard {
    all m1, m2: Move, p: Player, c: Card | playCard[m1, m2, p, c] implies {
        GameState.hands[m1][p][c] = True
        GameState.hands[m2][p][c] = False
        some i: Int | GameState.discard[m2][i] = c
    }
}
// Test that card playing follows the rules
test suite for playCard {
    assert all m1, m2: Move, p: Player, c: Card | { playCardMovesToDiscard } is necessary for playCard[m1, m2, p, c]
}