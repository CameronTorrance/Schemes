import misc.rationals.order

namespace manifolds

open rational

structure rational_cauchy :=
(seq : ℕ → ℚ)
(cauchy : ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ, ∀ {n m : ℕ}, n ≥ N  → m ≥ N →  
  rational_abs (seq n - seq m) < ε)

def is_rational_cauchy : (ℕ → ℚ) → Prop := λ seq,  ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ, ∀ {n m : ℕ}, 
  n ≥ N  → m ≥ N → rational_abs (seq n - seq m) < ε

def same_limit : rational_cauchy → rational_cauchy → Prop := λ f₁ f₂, ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ,
  ∀ {n : ℕ}, n ≥ N → rational_abs (f₁.seq n - f₂.seq n) < ε 

end manifolds