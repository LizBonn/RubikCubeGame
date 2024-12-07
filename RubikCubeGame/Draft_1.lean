import Mathlib.Tactic

-- Level 1, definition to law of group.
example {G : Type*} [Group G] (x y : G) : x * y = x * y := rfl

example {G : Type*} [Group G] (x y : G) : x * y = x * y := by rfl

-- Level 2, introduction to rw, theorems.
example {G : Type*} [Group G] (x y z : G) (h : x * y = y * x) : x * y * z = y * x * z := by
  rw [h]

example {G : Type*} [Group G] (x y z : G) : x * y * z = x * (y * z) := by
  rw [mul_assoc]
-- mul_assoc

example {G : Type*} [Group G] (x : G) : 1 * x = x := by
  rw [one_mul]
-- one_mul

example {G : Type*} [Group G] (x : G) : x * 1 = x := by
  rw [mul_one]
-- mul_one

example {G : Type*} [Group G] (x : G) : x⁻¹ * x = 1 := by
  rw [mul_left_inv]
-- mul_left_inv

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := by
  rw [mul_right_inv]
-- mul_right_inv

-- Level 3, introduction to intro.
example {G : Type*} [Group G] : ∀ x : G, x = x := by
  intro x
  rfl

-- Level 4, introduction to left arrow.
example {G : Type*} [Group G] (x : G) : ∀ y : G, y * x = 1 → y = x⁻¹ := by
  intro y h
  rw [← one_mul x⁻¹, ← h, mul_assoc, mul_right_inv, mul_one]



structure AddGroup₁ where
  add₁ : α → α → α
  add_assoc₁ : ∀ x y z : α, add₁ (add₁ x y) z = add₁ x (add₁ y z)
  zero₁ : α
  add_zero₁ : ∀ x : α, add₁ x zero₁ = x
  neg₁ : α → α
  add_neg₁ : ∀ x : α, add₁ x (neg₁ x) = zero₁

#check ZMod 3



instance instCommSemigroup (n : ℕ) : CommSemigroup (Fin n) :=
  { inferInstanceAs (Mul (Fin n)) with
    mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ =>
      Fin.eq_of_val_eq <|
        calc
          a * b % n * c ≡ a * b * c [MOD n] := (Nat.mod_modEq _ _).mul_right _
          _ ≡ a * (b * c) [MOD n] := by rw [mul_assoc]
          _ ≡ a * (b * c % n) [MOD n] := (Nat.mod_modEq _ _).symm.mul_left _
    mul_comm := Fin.mul_comm }

instance instCommRing (n : ℕ) [NeZero n] : CommRing (Fin n) :=
  { Fin.instAddMonoidWithOne n, Fin.addCommGroup n, Fin.instCommSemigroup n, Fin.instDistrib n with
    one_mul := Fin.one_mul'
    mul_one := Fin.mul_one',
    -- Porting note: new, see
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/ring.20vs.20Ring/near/322876462
    zero_mul := Fin.zero_mul'
    mul_zero := Fin.mul_zero' }


set_option pp.rawOnError true
example {G : Type*} [Group G] : ∀ x : G, x * x⁻¹ = 1 := by
  intro x
  have h : x * x⁻¹ = (x * x⁻¹)⁻¹ * (x * x⁻¹) * (x * x⁻¹) := by
    rw [mul_left_inv]
    rw [one_mul]
  rw [h]
  have (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by

    sorry
  sorry

#check Fin.add_zero
#check ZMod.cast_add
#check mul_inv

-- Level 5, ZMod is an additive group.
variable (n : ℕ)
#check ZMod n

structure Fin₁ (n : Nat) where
  /-- If `i : Fin n`, then `i.val : ℕ` is the described number. It can also be
  written as `i.1` or just `i` when the target type is known. -/
  val  : Nat
  /-- If `i : Fin n`, then `i.2` is a proof that `i.1 < n`. -/
  isLt : LT.lt val n

def ZMod₁ : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin₁ (n + 1)

-- Level 5, x : ZMod n, x.val < n + 1
example [NeZero n] (x : ZMod n) : x.val < n := by exact ZMod.val_lt x

example [NeZero n] (x : Fin n) : x.val < n := by exact x.isLt

example [NeZero n] (x : ZMod n) : x.val < n := by exact x.val_lt

example [NeZero n] (x : ZMod n) : x.val < n + 1 := by
  apply lt_trans x.val_lt
  exact lt_add_one n

#print Fin.add

example [NeZero n] (x : ZMod n) : x.val < n + 1 := by
  have : x.val < n := by
    exact ZMod.val_lt x
  apply lt_trans this
  exact Nat.lt_succ_self _


example (n : ℕ) [NeZero n] (x y : ZMod n) : ZMod n := by
  if h : n = 0 then
    subst h
    exact False.elim <| NeZero.ne 0 <| rfl
  else
    rw [show ZMod n = Fin n by sorry]
    sorry

example (n : ℕ) [NeZero n] (x : ZMod n) : 0 + x = x ∧ x + 0 = x := by
  constructor
  ·
    sorry
  ·
    sorry

example (n : ℕ) [NeZero n] (x : ZMod n) : x + -x = 0 := by
  rw [add_right_neg]

example (n : ℕ) [NeZero n] (x : ZMod n) : - x + x = 0 := by

  sorry


-- level 6
def ZMod_mk {n : ℕ} [NeZero n] (val : ℕ) (val_lt : val < n) : ZMod n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact ⟨val, val_lt⟩

theorem ZMod_mk_val {n : ℕ} [NeZero n] {val : ℕ} {val_lt : val < n} : (ZMod_mk val val_lt).val = val := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

example (n : ℕ) [NeZero n] (x y : ZMod n) : ZMod n := by
  refine ZMod_mk ((x.val + y.val) % n) ?_
  exact Nat.mod_lt _ (Nat.pos_iff_ne_zero.mpr (NeZero.ne n))

theorem ZMod_add_def {n : ℕ} [NeZero n] (x y : ZMod n) : (x + y).val = (x.val + y.val) % n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

theorem ZMod_neg_def {n : ℕ} [NeZero n] (x : ZMod n) : (-x).val = (n - x.val) % n := by
  cases n
  · exact False.elim <| NeZero.ne 0 rfl
  · exact rfl

variable (x : Fin 0)
variable (h : 0 = 1)

example (n : ℕ) : ZMod (n + 1) = Fin (n + 1) := rfl

example (x : Fin 0) : False := by
  admit

-- level 7
theorem ZMod_val_eq_iff_eq (n : ℕ) [NeZero n] (x y : ZMod n) : x.val = y.val ↔ x = y := by
  constructor
  · intro h
    exact ZMod.val_injective n (show ZMod.val x = ZMod.val y from h)
  · intro h
    rw [h]

example [NeZero n] (x : ZMod n): 0 + x = x ∧ x + 0 = x := by
  constructor
  · rw [← ZMod_val_eq_iff_eq n (0 + x) x]
    rw [ZMod_add_def]
    rw [ZMod.val_zero, zero_add]
    apply Nat.mod_eq_of_lt
    exact ZMod.val_lt x
  ·
    sorry

-- level 8

example (n : ℕ) [NeZero n] (x : ZMod n) : x + -x = 0 := by
  -- rw [← ZMod_val_eq_iff_eq n (x + -x) 0]
  apply (ZMod_val_eq_iff_eq n (x + -x) 0).mp
  -- show  (x.val + (n - x.val) % n) % n = 0
  rw [ZMod_add_def, ZMod_neg_def]
  simp only [Nat.add_mod_mod, ZMod.val_zero]
  -- have : x.val + (n - x.val) = n := by
  --   refine Nat.add_sub_of_le ?h
  --   exact ZMod.val_le x
  -- rw [this]
  rw [add_comm, Nat.sub_add_cancel (le_of_lt x.val_lt)]
  simp only [Nat.mod_self]

#check ZMod
#print Fin.add
#print Fin.neg

example (n x : ℕ) [NeZero n] [NeZero x] (h : x < n): (ZMod_mk x h).val = x := by
  exact ZMod_mk_val

-- example

example {G₁ G₂ : Type*} [Group G₁] [Group G₂] : G₁ × G₂ →* G₁ := by
  exact MonoidHom.fst G₁ G₂

-- example {G₁ G₂ : Type*} [Group G₁] [Group G₂] : Group (G₁ × G₂) where
--   mul := by
--     intro x y
--     exact ⟨x.1 * y.1, x.2 *y.2⟩
--   mul_assoc := by
--     intro x y z
--     ext
--     simp [Prod.fst_mul]
--     rw [mul_assoc]
--     simp [Prod.snd_mul]
--     rw [mul_assoc]
--   one := by
--     use 1, 1
--   one_mul := by
--     intro x
--     ext
--     rw [one_mul]
--     rw [one_mul]
--   mul_one := by
--     intro x
--     ext
--     rw [mul_one]
--     rw [mul_one]
--   inv := by
--     -- intro x
--     -- use x.1⁻¹
--     -- use x.2⁻¹
--     sorry
--   mul_left_inv := by
--     -- intro x
--     -- ext
--     -- rw [mul_left_inv]
--     -- rw [mul_left_inv]
--     sorry

-- example {G₁ G₂ : Type*} [Group G₁] [Group G₂] (g₁ : G₁) (g₂ : G₂) : fun ⟨g₁, g₂⟩ ↦ g₁ := by
--   exact MonoidHom.fst G₁ G₂
