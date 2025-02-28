import Game.Metadata

World "World_Three"
Level 5
Title "Definition of bijective function."

Statement {α β : Type} (f : α → β) : Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  rfl

Conclusion "Level Completed!"
NewTactic use
