import Mathlib

open Set

-- Level 1. Definition of subset.
example {α : Type*} (s t : Set α): s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by
  rfl

-- Level 2. A set is a subset of itself.
example {α : Type*} (s : Set α) : s ⊆ s := by
  intro x xs
  exact xs

-- Level 3. Containing relation is transitive.
example {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h₁ h₂ x hx
  apply h₂
  apply h₁
  exact hx

-- Level 4. Definition of intersection of sets.
example {α : Type*} (s t : Set α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  rw [mem_inter_iff]

-- Level 5. Definition of union of sets.
example {α : Type*} (s t : Set α) (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  simp only [mem_union]

-- Level 6. Intersection is commutative.
example {α : Type*} (s t : Set α): s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

-- Level 7. Union is associative.
example {α : Type*} (s t r : Set α): (s ∪ t) ∪ r = s ∪ (t ∪ r) := by
  ext x
  simp only [mem_union]
  tauto

-- Level 8.
example {α : Type*} (s t : Set α) : s ⊆ t → s ∩ t = s := by
  intro h
  ext x
  rw [mem_inter_iff]
  constructor
  exact fun ha ↦ ha.1
  exact fun ha ↦ ⟨ha, h ha⟩

-- Level 9. A subgroup of a group is a subset of the group.
example {G : Type*} [Group G] (H : Subgroup G) : H.carrier ⊆ ⊤ := by
  intro x _
  exact trivial

-- Level 10. Elements of a subgroup is closed under multiplication.
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H := by
  apply Subgroup.mul_mem H
  exact hx
  exact hy

-- Level 11. Intersection of subgroups is a subgroup.
example {G : Type*} [Group G] (H₁ : Subgroup G) (H₂ : Subgroup G) : Subgroup G where
  carrier := H₁.carrier ∩ H₂.carrier
  mul_mem' := by
    intro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    rw [mem_inter_iff]
    exact ⟨H₁.mul_mem' hx₁ hy₁, H₂.mul_mem' hx₂ hy₂⟩
  one_mem' := by
    simp
    exact ⟨H₁.one_mem, H₂.one_mem⟩
  inv_mem' := by
    simp

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

-- Let E be all possible states of a cube, Ex be all possible states of corners and Ey be all possible states of edges. Then E is the direct product of Ex and Ey, which is a finite set. We calculate the number of this set.
example {α : Type*} (Ex Ey : Set α) [Finite E] (h : E ≃ Ex × Ey) (hEx : Nat.card Ex = (Nat.factorial 8) * 3 ^ 8) (hEy : Nat.card Ey = (Nat.factorial 12) * 2 ^ 12) : Nat.card E = (Nat.factorial 12) * (Nat.factorial 8) * 3 ^ 8 * 2 ^ 12 := by
  rw [mul_assoc _ (Nat.factorial 8), ← hEx, mul_assoc, mul_comm (Nat.card Ex) , ← mul_assoc, ← hEy, mul_comm]
  rw [Nat.card_congr h, Nat.card_prod]
