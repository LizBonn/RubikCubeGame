import Game.Metadata

World "World_Three"
Level 7
Title "Possible states calculation."

Introduction "Let E be all possible states of a cube, Ex be all possible states of corners and Ey be all possible states of edges. Then E is the direct product of Ex and Ey, which is a finite set. We calculate the number of this set."

Statement {α : Type*} (Ex Ey : Set α) [Finite E] (h : E ≃ Ex × Ey) (hEx : Nat.card Ex = (Nat.factorial 8) * 3 ^ 8) (hEy : Nat.card Ey = (Nat.factorial 12) * 2 ^ 12) : Nat.card E = (Nat.factorial 12) * (Nat.factorial 8) * 3 ^ 8 * 2 ^ 12 := by
  rw [mul_assoc _ (Nat.factorial 8), ← hEx, mul_assoc, mul_comm (Nat.card Ex) , ← mul_assoc, ← hEy, mul_comm]
  rw [Nat.card_congr h, Nat.card_prod]


Conclusion "Level Completed!"
NewTheorem mul_comm Nat.card_congr Nat.card_prod
