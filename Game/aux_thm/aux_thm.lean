import Mathlib.Tactic

def ZMod_mk {n : ℕ} [NeZero n] (val : ℕ) (val_lt : val < n) : ZMod n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact ⟨val, val_lt⟩

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

theorem ZMod_neg_def {n : ℕ} [NeZero n] (x : ZMod n) : (-x).val = (n - x.val) % n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl
