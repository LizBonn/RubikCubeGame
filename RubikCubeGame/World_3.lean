import Mathlib

open Function

variable {α β γ : Type} (f : α → β) (g : β → γ)

example : Injective f ↔ ∀ x y, f x = f y → x = y := by
  rfl

example : Surjective f ↔ ∀ y, ∃ x, f x = y := by
  rfl

example : Bijective f ↔ Injective f ∧ Surjective f := by
  rfl

example (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  intro x y  h
  apply hf
  apply hg
  exact h

example (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  intro y
  rcases hg y with ⟨x, hx⟩
  rcases hf x with ⟨a, ha⟩
  use a
  rw [← hx, ← ha]
  rfl

example (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := by
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
