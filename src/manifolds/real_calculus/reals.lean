import misc.rationals

namespace manifolds

open rational

structure rational_cauchy :=
(seq : ℕ → ℚ)
(cauchy : ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ, ∀ {n m : ℕ}, N ≤ n → N ≤ m →  
  rational_abs (seq n - seq m) < ε)



end manifolds