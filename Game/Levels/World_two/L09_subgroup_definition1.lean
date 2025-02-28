import Game.Metadata

World "World_Two"
Level 9
Title "A subgroup of a group is a subset of the group."

Statement {G : Type*} [Group G] (H : Subgroup G) : H.carrier ⊆ ⊤ := by
  intro x _h
  exact trivial


Conclusion "Level Completed!"
NewTheorem trivial
