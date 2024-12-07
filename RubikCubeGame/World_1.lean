import Mathlib.Tactic

-- Level 1, definition to law of group.
-- New notions : multiplication in group, rfl
example {G : Type*} [Group G] (x y : G) : x * y = x * y := by rfl

-- Level 2, introduction to rw, hypothesis.
example {G : Type*} [Group G] (x y z : G) (h : x * y = y * x) : x * y * z = y * x * z := by
  rw [h]

#check mul_assoc
example {G : Type*} [Group G] (x y z : G) : x * y * z = x * (y * z) := by
  rw [mul_assoc]

#check one_mul
example {G : Type*} [Group G] (x : G) : 1 * x = x := by
  rw [one_mul]

#check mul_one
example {G : Type*} [Group G] (x : G) : x * 1 = x := by
  rw [mul_one]

#check mul_left_inv
example {G : Type*} [Group G] (x : G) : x⁻¹ * x = 1 := by
  rw [mul_left_inv]

#check mul_right_inv
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := by
  rw [mul_right_inv]


-- Level 3, introduction to intro.
-- New notion : intro
example {G : Type*} [Group G] : ∀ x : G, x = x := by
  intro x
  rfl

-- Level 4, introduction to left arrow.
-- New notion : left arrow
example {G : Type*} [Group G] (x y z : G) (h : y * z = x) : x = y * z := by
  rw [← h]

example {G : Type*} [Group G] (x : G) : ∀ y : G, y * x = 1 → y = x⁻¹ := by
  intro y h
  rw [← one_mul x⁻¹, ← h, mul_assoc, mul_right_inv, mul_one]

-- Level 5, x : ZMod n, x.val < n + 1
--New notion : exact
example {G : Type*} [Group G] (x y : G) (h : x = y) : x = y := by
  exact h

#check ZMod.val_lt
-- New notion : ZMod
example [NeZero n] (x : ZMod n) : x.val < n := by exact ZMod.val_lt x

-- New notion : apply
#check lt_trans
example (a b c : ℕ) (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans h1
  exact h2

#check lt_add_one
example [NeZero n] (x : ZMod n) : x.val < n + 1 := by
  apply lt_trans x.val_lt
  exact lt_add_one n

-- Level 6
def ZMod_mk {n : ℕ} [NeZero n] (val : ℕ) (val_lt : val < n) : ZMod n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact ⟨val, val_lt⟩

theorem ZMod_mk_val {n : ℕ} [NeZero n] {val : ℕ} {val_lt : val < n} : (ZMod_mk val val_lt).val = val := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

-- AddGroup
#check add_assoc
example {G : Type*} [AddGroup G] (x y z : G) : x + y + z = x + (y + z) := by
  rw [add_assoc]

#check zero_add
example {G : Type*} [AddGroup G] (x : G) : 0 + x = x := by
  rw [zero_add]

#check add_zero
example {G : Type*} [AddGroup G] (x : G) : x + 0 = x := by
  rw [add_zero]

#check add_right_neg
example {G : Type*} [AddGroup G] (x : G) : x + -x = 0 := by
  rw [add_right_neg]

#check add_left_neg
example {G : Type*} [AddGroup G] (x : G) : -x + x = 0 := by
  rw [add_left_neg]

-- New notion : definition of addition in ZMod n
#check Nat.mod_lt
#check Nat.pos_iff_ne_zero
#check NeZero.ne
example (n : ℕ) [NeZero n] (x y : ZMod n) : ZMod n := by
  apply ZMod_mk ((x.val + y.val) % n)
-- Maybe this line should be given in the game.
  apply Nat.mod_lt
  apply Nat.pos_iff_ne_zero.mpr
  apply NeZero.ne n

-- level 7
theorem ZMod_val_eq_iff_eq (n : ℕ) [NeZero n] (x y : ZMod n) : x.val = y.val ↔ x = y := by
  constructor
  · intro h
    exact ZMod.val_injective n (show ZMod.val x = ZMod.val y from h)
  · intro h
    rw [h]

theorem ZMod_add_def {n : ℕ} [NeZero n] (x y : ZMod n) : (x + y).val = (x.val + y.val) % n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

-- New notion : constructor
#check ZMod_val_eq_iff_eq
#check ZMod_add_def
#check ZMod.val_zero
#check Nat.mod_eq_of_lt
example [NeZero n] (x : ZMod n): 0 + x = x ∧ x + 0 = x := by
  constructor
  · rw [← ZMod_val_eq_iff_eq n (0 + x) x]
    rw [ZMod_add_def]
    rw [ZMod.val_zero, zero_add]
    apply Nat.mod_eq_of_lt
    exact ZMod.val_lt x
  · rw [← ZMod_val_eq_iff_eq]
    rw [ZMod_add_def]
    rw [ZMod.val_zero, add_zero]
    apply Nat.mod_eq_of_lt
    exact ZMod.val_lt x


-- level 8
theorem ZMod_neg_def {n : ℕ} [NeZero n] (x : ZMod n) : (-x).val = (n - x.val) % n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

#check add_comm
example {G : Type*} [AddCommGroup G] (x y: G) : x + y = y + x := by
  rw [add_comm]

#check add_right_neg
#check Nat.add_mod_mod
#check Nat.sub_add_cancel
#check le_of_lt
#check Nat.mod_self
example (n : ℕ) [NeZero n] (x : ZMod n) : x + -x = 0 := by
  -- rw [← ZMod_val_eq_iff_eq n (x + -x) 0]
  apply (ZMod_val_eq_iff_eq n (x + -x) 0).mp
-- This can be given in "Hint".
  rw [ZMod_add_def, ZMod_neg_def]
  rw [Nat.add_mod_mod, ZMod.val_zero]
  rw [add_comm, Nat.sub_add_cancel (le_of_lt x.val_lt)]
  rw [Nat.mod_self]

example (n : ℕ) [NeZero n] (x : ZMod n) : x + -x = 0 := by
  rw [add_right_neg]

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
