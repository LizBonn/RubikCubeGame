import Game.Metadata

World "World_Two"
Level 8
Title "Exercise"

Statement {α : Type*} (s t : Set α) : s ⊆ t → s ∩ t = s := by
  intro h
  ext x
  rw [Set.mem_inter_iff]
  constructor
  exact fun ha ↦ ha.1
  exact fun ha ↦ ⟨ha, h ha⟩


Conclusion "Level Completed!"
