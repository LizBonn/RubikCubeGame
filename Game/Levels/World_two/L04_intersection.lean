import Game.Metadata

World "World_Two"
Level 4

Title "Definition of intersection."

Statement {α : Type*} (s t : Set α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  rw [Set.mem_inter_iff]

Conclusion "Level Completed!"
NewTheorem Set.mem_inter_iff
