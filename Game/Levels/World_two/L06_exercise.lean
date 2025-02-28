import Game.Metadata

World "World_Two"
Level 6

Title "Intersection is commutative."

Statement {α : Type*} (s t : Set α): s ∩ t = t ∩ s := by
  ext x
  rw [Set.mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩


Conclusion "Level Completed!"
NewTactic ext rintro constructor
