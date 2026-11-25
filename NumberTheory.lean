import Mathlib

-- A prime number example
theorem two_is_prime : Nat.Prime 2 := by
  decide

-- Every natural number is either even or odd
theorem even_or_odd (n : ℕ) : Even n ∨ Odd n := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h
  · exact Or.inr h

-- Translation from informal to formal:
-- Informal: For all n, n is even or n is odd
-- Formal: ∀ n : ℕ, Even n ∨ Odd n
theorem forall_even_or_odd : ∀ n : ℕ, Even n ∨ Odd n := by
  intro n
  exact even_or_odd n
