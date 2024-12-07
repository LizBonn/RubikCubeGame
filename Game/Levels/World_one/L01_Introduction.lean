import Game.Metadata

World "World_One"
Level 1

Title "Group in Lean"

Introduction "First, we introduce how to define a group in Lean. Just use `(G : Type*) [Group G]`.

This defines `G` as a group. A group is a special set such that the elements of the group can be combined using a binary operation, which we will denote by `*`, which is defined as a mapping from `G ⨯ G` to `G`.

Groups satisfy four conditions:

(1) For any elements `a` and `b` in the group, `a * b` is also in the group — this follows from the definition of `*`.

(2) The associative property holds. For any `a`, `b`, `c` in `G`: `a * b * c = a * (b * c)`.

(3) There exists an identity element `1`. For any `a` in `G`: `1 * a = a * 1 = a`.

(4) Every element has an inverse. For any `a` in G: `a⁻¹ * a = 1`.

In this first level we're going to introduce the tactic `rfl` as well.
The tactic `rfl` proves all theorems of the form `X = X`.
Prove that `a * b = a * b` by executing the `rfl` tactic."

Statement (G : Type*) [Group G] (a b : G) : a * b = a * b := by
  Hint "In order to use the tactic `rfl`, you can enter it in the text box under the goal and hit \"Execute\""
  rfl

Conclusion "Congratulations! You completed your first verified proof!

Remember that `rfl` is a tactic.

If you ever want information about the `rfl` tactic, you can click on `rfl` in the list of tactics on the right.

Now click on \"Next\" to learn about the `rw` tactic."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
