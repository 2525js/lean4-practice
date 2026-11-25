import Mathlib

-- Proof by induction: n + 0 = n
theorem add_zero_by_induction (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.add_succ, ih]

-- Proof by induction: 0 + n = n
theorem zero_add_by_induction (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- If a statement holds for all n, it holds for n + 1
theorem succ_example (n : ℕ) : n + 1 = n + 1 := by
  rfl
