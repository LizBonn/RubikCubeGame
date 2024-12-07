import Game.Metadata

World "World_One"
Level 8

Title "ZMod negation"

Introduction "In this eighth level the goal is to prove each element in `ZMod n` has a right inverse.

The right inverse `-x` is defined by `(-x).val = (n - x.val) % n` and `(-x).val_lt : (n - x.val) % n < n`."

Statement (n : ℕ) [NeZero n] (x : ZMod n) : x + -x = 0 := by
  Hint "Can you take it from here?"
  Hint (hidden := true) "Try `rw [← ZMod_val_eq_iff_eq n (x + -x) 0]`."
  rw [← ZMod_val_eq_iff_eq n (x + -x) 0]
  rw [ZMod_add_def, ZMod_neg_def]
  rw [Nat.add_mod_mod, ZMod.val_zero]
  Hint "You need to rewrite theorems to prove it.

  Note that if a theorem has assumption as condition, you need to give it an input as assumption.

  For example, the theorem `Nat.sub_add_cancel` has assumption `(h : m ≤ n)`, so we need `rw Nat.sub_add_cancel h`.

  In this exercise, we need `rw Nat.sub_add_cancel (le_of_lt x.val_lt)`.

  Now try to prove this goal by yourself."
  rw [add_comm, Nat.sub_add_cancel (le_of_lt x.val_lt)]
  rw [Nat.mod_self]

Conclusion "Level completed! Remember that `ZMod n` has a right inverse. The proof that `ZMod n` has a left inverse is similar.

From the previous levels you can find that `ZMod n` is an additive commutative group.

It contains nature numbers less than `n` and its addition is modular addition.

For example, `ZMod 3 = {0, 1, 2}` , `1 + 2 = 3 (Mod 3) = 0`.

The orient state of a corner block of the cube can actually be represented by `ZMod 3`.

The original orient state is denoted as `0`, the state after the 120° clockwise rotation is `1`, the state after the 240° clockwise rotation is `2`, and the state is restored to `0` after the third rotation.

Similarly, the orient state of a edge block of the cube can actually be represented by `ZMod 2`.

We can use 8 natural numbers less than 3 to represent the corner block orient information of the cube, and 12 natural numbers less than 2 to represent the edge block orient information of the cube."

NewTheorem ZMod_neg_def Nat.add_mod_mod add_comm Nat.sub_add_cancel le_of_lt Nat.mod_self
