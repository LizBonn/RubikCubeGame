import Game.Metadata

World "World_One"
Level 7

Title "ZMod zero element"

Introduction "In this seventh level is to prove that there is a null element in the `ZMod n`.

Now try to prove this goal by yourself."

Statement (n : ℕ) [NeZero n] (x : ZMod n): 0 + x = x := by
  Hint "Can you take it from here?"
  Hint (hidden := true) "Try `rw [← ZMod_val_eq_iff_eq n (0 + x) x, ZMod_add_def, ZMod.val_zero, zero_add,Nat.mod_eq_of_lt]`."
  rw [← ZMod_val_eq_iff_eq n (0 + x) x]
  rw [ZMod_add_def]
  rw [ZMod.val_zero]
  rw [zero_add]
  rw [Nat.mod_eq_of_lt]
  exact x.val_lt

Conclusion "Level completed! Remember that `ZMod n` has a left null element.

The proof that `ZMod n` has a right null element is similar.

Let's continue the journey."

NewTheorem ZMod_val_eq_iff_eq ZMod_add_def ZMod.val_zero zero_add Nat.mod_eq_of_lt
