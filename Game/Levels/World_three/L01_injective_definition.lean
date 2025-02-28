import Game.Metadata

World "World_Three"
Level 1
Title "Definition of injective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) : Function.Injective f ↔ ∀ x y, f x = f y → x = y := by
  rfl


Conclusion "Level Completed!"
