import Game.Metadata

World "World_Two"
Level 7
Title "Union is associative"

Statement {α : Type*} (s t r : Set α): (s ∪ t) ∪ r = s ∪ (t ∪ r) := by
  ext x
  rw [Set.mem_union]
  constructor
  · rintro (h | h)
    · rw [Set.mem_union] at *
      rcases h with h | h
      · left
        exact h
      · right
        rw [Set.mem_union]
        left
        exact h
    · rw [Set.mem_union, Set.mem_union]
      right
      right
      exact h
  · rintro (h | h)
    · left
      rw [Set.mem_union]
      left
      exact h
    · rw [Set.mem_union] at *
      rcases h with h | h
      left
      right
      exact h
      right
      exact h


Conclusion "Level Completed!"
NewTactic left right
