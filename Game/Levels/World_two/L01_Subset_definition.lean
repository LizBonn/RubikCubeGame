import Game.Metadata

World "World_Two"
Level 1

Title "Subset in Lean"

Statement {α : Type*} (s t : Set α): s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by
  rfl

Conclusion "Level Completed!"
