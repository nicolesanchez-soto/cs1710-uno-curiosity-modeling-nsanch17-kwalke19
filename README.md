### **Curiosity**  

#### **Project Objective**  
This project models a **simplified version of UNO**, a popular multiplayer card game where players take turns discarding cards that match the color or value of the top discard pile card. The game includes **number cards (0-9), special action cards (Skip, Reverse, Draw Two), and Wild cards (which allow color changes and special effects).**  

However, due to **Forge's performance limitations**, we had to **drastically reduce** the scope of our model:
- **Fewer players:** We modeled a **2-player version** instead of the standard 4+ players.
- **Reduced deck size:** Instead of **108 cards**, we limited it to **19 cards** by:
  - Only including **three colors** (Red, Blue, Green) and **omitting Yellow** to reduce computational overhead.
  - Limiting number cards to **0-2** instead of the full **0-9** range.
  - Only modeling **two action cards (Skip, Draw Two)** instead of all **three** (Reverse is missing).
  - Reducing **Wild and Wild Draw Four** cards to **two copies** instead of the standard **four**.
- **Limited game length:** To prevent **excessive execution times**, we restricted the model to simulate **at most six turns** in a game trace.

##### **What We Would Have Done in a Full Model**
If Forge could handle larger and more complex models, we would have:  
- **Modeled a full 108-card deck**, including all **number cards (0-9) and all four colors (Red, Blue, Green, Yellow)**.  
- **Supported 4+ players**, implementing **turn rotation logic** for dynamic player numbers.  
- **Included Reverse and Challenge mechanics**, which introduce more strategic depth.  
- **Simulated longer games**, allowing more than six moves before Forge crashes.  

Because Forge struggled with **more than two players, a larger deck, or extended runs**, we had to make trade-offs in scope.  

---

### **Model Design and Visualization**  

Our model is designed to **simulate a turn-based, two-player version of UNO** while ensuring that each move correctly follows the game’s rules. Since Forge struggles with large-scale simulations, we had to carefully design the model to balance **accuracy and performance efficiency**. The core of our approach is the **GameState signature**, which acts as a **global tracker** for the deck, discard pile, player hands, turn order, and action card effects. To model turn-based progression, we use a **sequence of Move instances**, where each Move represents a distinct turn in the game. The `next` relation ensures that the game progresses linearly, as Forge’s performance issues made it infeasible to support complex branching paths for turn order adjustments, such as those caused by Reverse cards.  

A key aspect of our design is **card validity enforcement**. We define a `validCard` predicate that ensures **Wild cards have no preassigned color**, while all other cards must have exactly one color. We also enforce a `validCardSpread` predicate to **simulate deck constraints**, ensuring that cards exist in limited numbers while keeping the game computationally feasible. Because we couldn’t include the full 108-card deck, we carefully selected a **subset of number cards (0-2), action cards (Skip, Draw Two), and Wild cards (Wild, Wild Draw Four)** while omitting Yellow to simplify the model.  

To verify that the game follows valid transitions, we wrote **several run statements** to check different aspects of the game’s execution. One of the primary runs focuses on a **short game trace**, where we track how cards move through the deck, hands, and discard pile over a few moves. This run ensures that:
1. The game **initializes correctly**, with each player receiving **exactly 7 cards**.  
2. Players **can only play valid cards**, meaning a card must match **the color or value** of the top discard pile card unless it is a Wild.  
3. **Action cards behave correctly**, ensuring that Skip prevents the next player’s turn, Draw Two forces the opponent to take extra cards, and Wild cards allow for **color selection**.  
4. The **game ends properly** when a player runs out of cards, ensuring that no additional moves occur beyond that point.  

For visualization, we relied on **Forge’s default Sterling visualizer**, which provides a **graph-based representation of the game state**. In an instance produced by our spec, you will see nodes representing **Players, Cards, Moves, and GameState**, with directed edges showing relationships such as:
- **Which cards belong to which players** (hands).  
- **Which card is on the top of the discard pile**.  
- **Who the current player is at each move**.  
- **Pending action cards and their effects**.  

To interpret an instance in Sterling, the first thing to look at is **the discard pile**, which helps identify the game’s progression and determine what legal moves are available. Next, examining the **current player at a given move** shows whose turn it is and which cards they can play. If an action card was played, the **pending action relation** will indicate whether the next player is affected (e.g., needing to draw two cards). Additionally, when a Wild card is played, the **chosenColor mapping** will show the new active color.  

Unlike a real game UI that might display cards in a structured table format, the Sterling visualization presents the game’s state as a **set of relational mappings**. This means interpreting the instance requires analyzing **node relationships** rather than viewing a traditional card table layout. Although we did not create a custom visualization due to Forge’s constraints, the default Sterling visualizer is sufficient for **validating the logical structure of the game** and ensuring that all game states follow the intended rules.  

If we had the capability to extend visualization, we would have created a **custom graphical representation** showing the **deck, discard pile, and player hands in a more intuitive format**, possibly using color-coded edges to indicate playable moves. However, given the limitations of Forge’s rendering capabilities, we focused on **ensuring our model’s correctness through logical state tracking** rather than investing in additional visual customization.

---

### **Signatures and Predicates**  
**Key Signatures (`sig`)**  
- **`Player`** – Represents individual players in the game.  
- **`Move`** – Represents a turn in the game, linked in a **linear sequence** to avoid performance issues.  
- **`Card`** – Represents UNO cards, each with a **value (number, action, or wild) and an optional color**.  
- **`Color`** – Defines **three colors** (Red, Blue, Green) due to performance limitations.  
- **`Value`** – Defines available card types:
  - **Number cards (0-2)**
  - **Action cards (Skip, Draw Two)**
  - **Wild cards (Wild, Wild Draw Four)**
- **`GameState`** – The central state tracker that maintains:
  - **Deck composition**
  - **Discard pile order**
  - **Player hands**
  - **Current turn**
  - **Pending effects of action cards**  

##### **Limitations Due to Simplification**
- **No Reverse cards**: We omitted the **Reverse** mechanic because its logic (flipping turn order) is complex in a **linear move-based model**.  
- **No Challenge Mechanic**: In a full model, a Wild Draw Four could trigger a **challenge**, which is unmodeled here.  
- **No Multiplayer Complexity**: In real UNO, players can **stack Draw Two/Wild Draw Four effects**—this is **not modeled** in our simplified version.  

##### **What We Would Have Done in a Full Model**
- **Fully model all card values, including Reverse.**  
- **Support challenge mechanics** for Wild Draw Four.  
- **Dynamically determine next player** (instead of linear move sequences).  

---

### **Testing**  

**Testing Overview**

The testing process for this Forge-based game model ensures that core game mechanics function as expected. Each test suite verifies a specific aspect of game behavior, including deck handling, player turns, card validity, action resolution, and game completion. The test cases systematically explore both valid and invalid game states to ensure constraints are properly enforced and to prevent unintended behavior.

**Card Validity and Distribution**

The `validCard` test suite ensures that only properly formed cards exist within the game. It verifies that regular cards have a color and value while wild cards lack a predefined color. Additionally, the `properNumberSpread` test checks that the deck contains the correct number of cards for each category (colors, values, and action types). By enforcing these constraints, we prevent under- or over-representation of specific card types and ensure the deck follows the intended distribution.

**Deck and Hand Management**

The `deal` test suite verifies that each player starts with exactly seven cards. This ensures compliance with initial game setup rules. The `drawCard` test suite evaluates whether drawing a card removes it from the deck and places it in a player's hand while keeping all other deck elements unchanged. The `addToHand` test confirms that cards can only be added from the deck and are removed from the deck afterward. Together, these tests maintain proper deck and hand state integrity.

**Turn and Play Mechanics**

The `playCard` test suite ensures that when a card is played, it moves from a player's hand to the discard pile, and the deck remains unchanged. It also verifies that special card actions (like wild cards) set appropriate game states. The `canPlayCard` test confirms that a card may only be played if it matches the top discard card’s color, value, or previously chosen wild card color.

The `playerTurn` test suite verifies that players take valid actions during their turns. If a player has no playable cards, they must draw instead of attempting an illegal play. This suite also ensures that no player can pass their turn without taking an action. Additionally, tests were conducted to verify that illegal plays (e.g., playing a card that does not match the discard pile) are **properly rejected**, maintaining game integrity.

**Action Resolution**

The `resolveAction` test suite checks that special card effects (such as skipping a turn, drawing extra cards, or choosing a wild color) are correctly applied. It ensures that after an action is resolved, the pending action queue is cleared to allow the game to proceed. This includes verifying that:
- Skip cards correctly prevent the next player from taking a turn.
- Draw Two and Wild Draw Four cards force the opponent to draw the correct number of cards before proceeding.
- Wild cards allow players to choose a valid new color.
- Pending actions are properly cleared after they are resolved.

The `skipAction` test confirms that skipping correctly advances the game state while preserving other elements. The `drawTwoAction` and `wildDrawFourAction` test suites validate that affected players receive the correct number of additional cards and that the turn flow remains intact.

**Game Flow and Completion**

The `moveNextPlayer` test suite ensures that turn order is correctly maintained, preventing multiple players from being active at once. The `skipOver` test validates that skip actions properly transition the turn to the next player. These tests confirm that turn sequencing is correctly enforced in both normal and action-card-affected scenarios.

The `gameOver` test suite determines whether the game ends when a player has no cards left and no valid future moves exist. It prevents premature termination or continued play when a player should have won. Additionally, tests were performed to verify that the game does **not** falsely declare an end if a valid move remains.

By ensuring these rules are rigorously tested, we maintain the integrity of the game model and prevent inconsistencies in gameplay logic. Furthermore, by testing both **valid and invalid states**, we ensure that constraints are properly enforced and that unintended behaviors do not arise during execution.

##### **What We Would Have Tested in a Full Model**
- **Turn Reversals** (Reverse card logic).  
- **Stacking Draw Cards** (e.g., stacking multiple Draw Twos).  
- **Multiplayer dynamics**, ensuring proper **turn sequencing** in a 4-player game.  

---

### **Documentation**  
We made sure that our model and test files are **well-documented**:
- **Inline comments** explaining key mechanics and constraints.  
- **Section headers** separating core predicates.  
- **Clear notation of Forge limitations** (such as 2-player restriction, simplified deck, and reduced move count).  

##### **What We Would Have Documented in a Full Model**
- **More detailed player interactions** (highlighting possible challenge strategies).  
- **Edge case behaviors** (e.g., what happens when all cards in the deck are used).  
- **Detailed visualization guide** (explaining the graphical representation of turns).  

---
### **Final Thoughts**  

This model successfully captures the **core gameplay mechanics of UNO**, allowing for a structured simulation of **card play, turn sequencing, and action card effects**. However, due to **Forge’s performance constraints**, we had to significantly limit the game's complexity. The most notable restrictions include **a reduced deck size**, **a two-player limit**, **simplified card mechanics**, and **a short game trace** that prevents extended gameplay. These limitations were necessary because Forge struggles to generate and process all possible states in a full UNO game, especially when modeling **more than two players, a full 108-card deck, and long turn sequences**.  

One of the biggest compromises was the **deck size reduction**. In real UNO, the deck consists of **four colors (Red, Blue, Green, Yellow) and number cards ranging from 0 to 9,** along with multiple copies of each card. Due to Forge’s **difficulty in handling a large state space**, we had to **omit Yellow entirely**, **limit number cards to 0-2 instead of 0-9**, and **reduce action and Wild cards** to just a few copies. This drastically simplified the card distribution while still maintaining the **core gameplay mechanics of matching colors and values**.  

Additionally, the **two-player restriction** meant that we could not fully implement **turn rotation logic for a larger game**. In a real UNO game, players take turns in a circular order, but Forge's tendency to crash when handling **multiple sequential turns** forced us to simplify this into a **strict two-player alternating sequence**. This limitation also affected **action card behaviors**—for example, **Reverse** was left out since it **doesn’t have an effect in a two-player game**. Moreover, Forge’s execution time made it **impractical to model longer games**, so we were limited to simulating **only a few moves before the system became too slow or crashed entirely**.  

Despite these constraints, our model **correctly enforces UNO’s core rules**. Players can **only play valid cards based on the top of the discard pile**, Wild cards correctly **trigger color selection**, action cards like **Skip and Draw Two function as intended**, and the game **ends when a player has no cards left**. We also ensured that all **cards are properly distributed, played, or drawn according to game rules**, allowing for a **valid yet restricted** simulation of a UNO match.  

If Forge had the capacity to handle a **more extensive model**, we would have expanded our implementation to include **all 108 cards, support for four or more players, proper turn rotation, and additional game mechanics such as stacking Draw cards and Wild Draw Four challenges**. A fully extensive version would have also allowed for **longer and more realistic gameplay simulations**, tracking complex interactions across multiple rounds. Unfortunately, Forge’s limitations meant we had to make **trade-offs between accuracy and feasibility**, but within these constraints, our model provides a **functional and verifiable two-player version of UNO** that correctly simulates the **core experience of the game** while maintaining logical correctness.  

### **Key Limitations and Trade-offs:**  
- **Deck size reduction:** 19 cards instead of 108, limited to three colors (Yellow omitted).  
- **Simplified number cards:** Only **0-2** instead of the full **0-9** range.  
- **Two-player restriction:** No support for **four or more players** due to execution limits.  
- **Short game length:** Maximum of **six turns** before Forge crashes.  
- **Omitted mechanics:** No **Reverse card, stacking Draw Twos, or Wild Draw Four challenges**.  

### **Despite These Limitations, Our Model Successfully:**  
- **Enforces UNO’s core matching rules (color and value-based plays).**  
- **Handles action cards (Skip, Draw Two, Wild, Wild Draw Four) correctly.**  
- **Ensures proper card distribution and tracking.**  
- **Implements valid turn progression within a restricted two-player setup.**  
- **Detects game-ending conditions when a player has no cards left.**  

In conclusion, while we could not model **a full UNO game** due to computational constraints, our design effectively **simulates a functional, rule-abiding two-player version**. With more **computational resources or a different modeling tool,** we would have been able to **scale this up to a full multiplayer game with all mechanics intact**. However, given Forge’s limitations, this model is a **proof-of-concept** that demonstrates the feasibility of modeling turn-based card games within a constrained environment.