import Game.Metadata

World "World_Three"
Level 6
Title "Composition of surjective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (g ∘ f) := by
  constructor
  · intro x y h
    apply hf.1
    apply hg.1
    exact h
  · intro y
    rcases hg.2 y with ⟨x, hx⟩
    rcases hf.2 x with ⟨a, ha⟩
    use a
    rw [← hx, ← ha]
    rfl

Conclusion "Level Completed!"
