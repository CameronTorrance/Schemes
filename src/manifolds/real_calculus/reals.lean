import misc.rationals.order

namespace manifolds

structure rational_cauchy :=
(seq : ℕ → ℚ)
(cauchy : ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ, ∀ {n m : ℕ}, n ≥ N  → m ≥ N →  
  rational.abs (seq n - seq m) < ε)

def is_rational_cauchy : (ℕ → ℚ) → Prop := λ seq,  ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ, ∀ {n m : ℕ}, 
  n ≥ N  → m ≥ N → rational.abs (seq n - seq m) < ε

def same_limit : rational_cauchy → rational_cauchy → Prop := λ f₁ f₂, ∀ {ε : ℚ}, ε > 0 → ∃ N : ℕ,
  ∀ {n : ℕ}, n ≥ N → rational.abs (f₁.seq n - f₂.seq n) < ε 

theorem same_limit_refl : ∀ f : rational_cauchy, same_limit f f :=
begin
  intros f ε hε,
  existsi 0,
  intros n hn,
  simp[comm_ring.minus_inverse,rational.abs_zero],
  assumption,
end

theorem same_limit_symm : ∀ f₁ f₂ : rational_cauchy, same_limit f₁ f₂ → same_limit f₂ f₁ :=
  sorry


end manifolds