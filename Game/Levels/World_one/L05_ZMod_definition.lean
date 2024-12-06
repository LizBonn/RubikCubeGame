import Game.Metadata

World "World_One"
Level 5

Title "ZMod Definition"

Introduction "The next levels will introduce a concrete example of group called `ZMod n`.

In lean, we define `ZMod: ℕ → Type`, so `ZMod n` is a type.

If `n = 0`, `ZMod n` is `ℤ`. If `n > 0`, `ZMod n` equals `Fin n` that is both type and structure.

As a structure, `Fin n` contains two types of value: `val` and `isLt`.

For example, if `x : Fin n`, `x.val` is the value of `x` and `x.isLt` is a proof saying `x < n`.

So all elements in `Fin n` are `Nat` less than `n`.

We use `[NeZero n]` to show `n` doesn't equal zero.

Note that when `x : ZMod n` and `NeZero n`, the proof `x < n` is represented by `x.val_lt`.

In this fifth level we 're going to introduce the tactic `exact` as well.

The tactic `exact e` closes the main goal if its target type matches that of `e`.
Prove that `x.val < n` by executing the `exact` tactic."

Statement (n : ℕ) [NeZero n] (x : ZMod n) : x.val < n := by
  Hint "Can you take it from here?"
  Hint (hidden := true) "Try `exact x.val_lt`."
  exact x.val_lt

Conclusion"Level completed!

Remember that `ZMod n (n ≠ 0)` equals the set of natural numbers less than `n` now.

Let's continue the journey."

NewTactic exact
