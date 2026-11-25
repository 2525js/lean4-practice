import Mathlib

-- Basic proofs about natural numbers
theorem add_zero_example (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]

theorem add_one_example (n : ℕ) : n + 1 = Nat.succ n := by
  rfl

theorem two_plus_two : (2 : ℕ) + 2 = 4 := by
  rfl

-- Proof that sum of two even numbers is even
theorem even_add_even {a b : ℕ} (ha : Even a) (hb : Even b) :
    Even (a + b) := by
  rcases ha with ⟨m, rfl⟩
  rcases hb with ⟨n, rfl⟩
  use m + n
  ring
