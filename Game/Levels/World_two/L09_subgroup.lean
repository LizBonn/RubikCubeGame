import Game.Metadata

World "World_Two"
Level 9
Title "Exercise"

Statement {G : Type*} [Group G] (H : Subgroup G) : H.carrier ⊆ ⊤ := by
  intro x _
  exact trivial


Conclusion "Level Completed!"
NewTheorem trivial
