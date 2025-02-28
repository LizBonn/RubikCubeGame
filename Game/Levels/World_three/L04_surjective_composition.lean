import Game.Metadata

World "World_Three"
Level 4
Title "Composition of surjective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
  intro y
  rcases hg y with ⟨x, hx⟩
  rcases hf x with ⟨a, ha⟩
  use a
  rw [← hx, ← ha]
  rfl

Conclusion "Level Completed!"
NewTactic use
