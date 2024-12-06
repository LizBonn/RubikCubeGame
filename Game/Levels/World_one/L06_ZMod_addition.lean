import Game.Metadata

World "World_One"
Level 6

Title "ZMod addition"

Introduction "In this sixth level we need to define proper addition in `ZMod n` to let it turns into an additive group.

We use `+` to represent the addition in `ZMod n`, and let `(x + y).val = (x.val + y.val) % n`, `(x + y).val_lt : (x.val + y.val) % n < n`.

In lean, we define a function called `ZMod_mk`, which can acquire an argumnet `n` and construct `ZMod n`."

Statement (n : ℕ) [NeZero n] (x y : ZMod n) : ZMod n := by
  Hint "First, use `refine ZMod_mk ((x.val + y.val) % n) ?_` to tell Lean that, we define the sum to be `(x.val + y.val) % n`."
  refine ZMod_mk ((x.val + y.val) % n) ?_
  Hint "Can you take it from here?"
  Hint (hidden := true) "Try `apply Nat.mod_lt`."
  apply Nat.mod_lt
  apply Nat.pos_iff_ne_zero.mpr
  apply NeZero.ne n


Conclusion "Level completed!

Remember that addition of `ZMod n (n ≠ 0)` equals the addition within the `Mod n`.

Let's continue the journey."

NewTactic refine apply
NewTheorem ZMod_mk Nat.mod_lt Nat.pos_iff_ne_zero NeZero.ne
