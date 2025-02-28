import Game.Metadata

World "World_Two"
Level 10
Title "Elements of a subgroup is closed under multiplication."

Statement {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H := by
  apply Subgroup.mul_mem H
  exact hx
  exact hy


Conclusion "Level Completed!"
NewTheorem Subgroup.mul_mem
