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

