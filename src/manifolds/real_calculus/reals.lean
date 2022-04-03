import misc.rationals.order

namespace manifold

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
begin
  intros f₁ f₂ h ε hε,
  cases h hε with Nε hNε,
  existsi Nε,
  intro,
  rw [rational.sub_antisymm, rational.abs_minus],
  apply hNε,
end

theorem same_limit_trans : ∀ f₁ f₂ f₃ : rational_cauchy, same_limit f₁ f₂ → same_limit f₂ f₃
  → same_limit f₁ f₃ :=
begin
  intros f₁ f₂ f₃ h12 h23,
  intros ε hε,
  cases hε with hε nε,
  cases hε with n hε,
  cases hε with m hε,
  simp[comm_ring.minus_zero_zero, comm_ring.add_zero] at hε,
  cases h12 (rational.scale_pos_rat 2 nε hε) with N₁ hN₁,
  cases h23 (rational.scale_pos_rat 2 nε hε) with N₂ hN₂,
  existsi max N₁ N₂,
  intros n hn,
  simp,
  rw comm_ring.add_midpoint (f₂.seq n),
  rw [hε, rational.mul_two_div_rat_by_two],
  apply rational.le_then_lt_lt,
  apply rational.triangle_inequality,
  apply rational.lt_add,
  apply hN₁,
  apply le_trans,
  apply le_max_left,
  exact N₂,
  assumption,
  apply hN₂,
  apply le_trans,
  apply le_max_right,
  exact N₁,
  assumption,
end
  
instance rational_cauchy_setiod : setoid rational_cauchy 
  := ⟨same_limit, same_limit_refl, same_limit_symm, same_limit_trans⟩

@[simp]
theorem rational_cauchy_eqv_concrete_char : ∀ f₁ f₂ : rational_cauchy, f₁ ≈ f₂ ↔ ∀ {ε : ℚ}, ε > 0 → 
  ∃ N : ℕ, ∀ {n : ℕ}, n ≥ N → rational.abs (f₁.seq n - f₂.seq n) < ε := λ _ _, by refl 

def real : Type := quotient manifold.rational_cauchy_setiod

notation `ℝ` := real 

def rational_cauchy_add : rational_cauchy → rational_cauchy → rational_cauchy := λ f₁ f₂,
{
  seq := λ n : ℕ, f₁.seq n + f₂.seq n,
  cauchy :=
    begin
      intros ε hε,
      cases hε with hε nε,
      cases hε with n hε,
      cases hε with m hε,
      simp[comm_ring.minus_zero_zero,comm_ring.add_zero] at hε,
      cases f₁.cauchy ((rational.scale_pos_rat 2 nε hε)) with N₁ hN₁,
      cases f₂.cauchy ((rational.scale_pos_rat 2 nε hε)) with N₂ hN₂,
      existsi max N₁ N₂,
      intros n' m' hn hm,
      simp[comm_ring.minus_dis,comm_ring.add_assoc₄,comm_ring.add_comm (f₂.seq n')],
      rw [← comm_ring.add_assoc₄,hε,rational.mul_two_div_rat_by_two],
      apply rational.le_then_lt_lt,
      apply rational.triangle_inequality,
      apply rational.lt_add,
      apply hN₁,
      apply le_trans,
      apply le_max_left,
      exact N₂,
      assumption,
      apply le_trans,
      apply le_max_left,
      exact N₂,
      assumption,
      apply hN₂,
      apply le_trans,
      apply le_max_right,
      exact N₁,
      assumption,
      apply le_trans,
      apply le_max_right,
      exact N₁,
      assumption,
    end,
}

instance rational_cauchy_has_add : has_add rational_cauchy := ⟨rational_cauchy_add⟩

@[simp]
theorem rational_cauchy_add_concrete_char : ∀ (f₁ f₂ : rational_cauchy) (n : ℕ) , 
  (f₁ + f₂).seq n = f₁.seq n + f₂.seq n := λ f₁ f₂ n, rfl 

def real_add : ℝ → ℝ → ℝ :=
begin
  apply quotient.lift₂ (λ f₁ f₂ : rational_cauchy, ⟦f₁ + f₂⟧),
  simp,
  intros f₁ f₂ g₁ g₂ h₁ h₂,
  apply quotient.sound,
  simp,
  intros ε hε,
  cases hε with hε nε,
  cases hε with n hε,
  cases hε with m hε,
  simp[comm_ring.minus_zero_zero,comm_ring.add_zero] at hε,
  cases h₁ ((rational.scale_pos_rat 2 nε hε)) with N₁ hN₁,
  cases h₂ ((rational.scale_pos_rat 2 nε hε)) with N₂ hN₂,
  existsi max N₁ N₂,
  intros n' hn',
  rw [hε,rational.mul_two_div_rat_by_two],
  rw [comm_ring.minus_dis, comm_ring.add_assoc₄, comm_ring.add_comm (f₂.seq n')],
  rw ← comm_ring.add_assoc₄,
  apply rational.le_then_lt_lt,
  apply rational.triangle_inequality,
  apply rational.lt_add,
  apply hN₁,
  apply le_trans,
  apply le_max_left,
  exact N₂,
  assumption,
  apply hN₂,
  apply le_trans,
  apply le_max_right,
  exact N₁,
  assumption,
end

instance real_has_add : has_add ℝ := ⟨real_add⟩ 

theorem real_add_concrete_char : ∀ x y : rational_cauchy, (⟦x⟧ + ⟦y⟧ : ℝ) = ⟦x + y⟧ := λ _ _, rfl


end manifold