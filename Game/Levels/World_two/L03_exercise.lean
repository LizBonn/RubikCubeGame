import Game.Metadata

World "World_Two"
Level 3

Title "Containing relation is transitive."

Statement {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h₁ h₂ x hx
  apply h₂
  apply h₁
  exact hx

Conclusion "Level Completed!"
