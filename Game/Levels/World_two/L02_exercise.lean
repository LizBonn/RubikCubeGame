import Game.Metadata

World "World_Two"
Level 2

Title "Containing relation is reflexive."

Statement {α : Type*} (s : Set α) : s ⊆ s := by
  intro x xs
  exact xs

Conclusion "Level Completed!"
