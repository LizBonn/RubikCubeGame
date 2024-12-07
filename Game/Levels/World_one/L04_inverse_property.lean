import Game.Metadata

World "World_One"
Level 4

Title "inverse_property"

Introduction "You may have noticed that we used the lemma `mul_right_inv` in the last level.

It says `(a : G) : a * a⁻¹ = 1`, while the definition of inv `x⁻¹` in group `G` is `(a : G): a⁻¹ * a = 1`.

In this fourth level the goal is to prove `∀ x : G, x * x⁻¹ = 1`, which means left inverse equals right inverse in a group."

Statement (G : Type*) [Group G] : ∀ x : G, x * x⁻¹ = 1 := by
  Hint "You can find that this prop with `∀` is no longer in the form of `Prop → Prop`.

  That means you just need to arbitrarily get an element from `G` without getting an assumption.

  So just execute `intro x` is Okay. It means `(x : G)`, while `x` is arbitrary."
  intro x
  Hint "Note that if you want to tell lean to change `x * x⁻¹` in the goal by giving `← one_mul` an input `x * x⁻¹`, please put it in the parentheses. Can you take it from here?"
  Hint (hidden := true) "Try `rw [← one_mul (x * x⁻¹)]`"
  rw [← one_mul (x * x⁻¹)]
  Hint "If you want to rewrite the nth target conform to the form, just replace `rw` with `nth_rw n`.

  For example, `nth_rw 1` rewrite the first target conform to the form.

  Let's now try to solve this goal."
  Hint (hidden := true) "Try `nth_rw 1 [← mul_left_inv x⁻¹]` and then `rw [mul_assoc x⁻¹⁻¹ x⁻¹ (x * x⁻¹), ← mul_assoc x⁻¹  x  x⁻¹]`"
  nth_rw 1 [← mul_left_inv x⁻¹]
  rw [mul_assoc x⁻¹⁻¹ x⁻¹ (x * x⁻¹)]
  rw [← mul_assoc x⁻¹ x x⁻¹]
  rw [mul_left_inv x]
  rw [one_mul]
  rw [mul_left_inv]

Conclusion "Level completed! Let's continue the journey."

NewTactic nth_rw
NewTheorem mul_left_inv
