import Game.Metadata

World "World_Three"
Level 2
Title "Composition of injective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  intro x y  h
  apply hf
  apply hg
  exact h


Conclusion "Level Completed!"
