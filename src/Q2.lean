import data.nat.prime

open nat 
-- the statement that there are arbitrarily long arithmetic progressions of primes
-- let N be the length of the arithmetic progression
-- let d be the difference between the terms
-- let t₀ be the starting integer
theorem green_tao : Prop := ∀ N d : ℕ, ∃ t₀, prime t₀ ∧ (∀ k < N, prime (t₀ + k*d))




