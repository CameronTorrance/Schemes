import algebra.comm_rings.instances.basic
import misc.rationals.pos_nat

namespace rational

def same_ratio : ℤ × ℕ⁺ → ℤ × ℕ⁺ → Prop 
| (z₁,n₁) (z₂,n₂) := z₁ * n₂ = z₂ * n₁ 

theorem same_ratio_refl : ∀ p : ℤ × ℕ⁺, same_ratio p p :=
begin
  intro p,
  cases p with z n,
  simp[same_ratio],
end

theorem same_ratio_symm : ∀ p₁ p₂ : ℤ × ℕ⁺, same_ratio p₁ p₂ → same_ratio p₂ p₁ :=
begin
  intros p₁ p₂,
  cases p₁ with z₁ n₁,
  cases p₂ with z₂ n₂,
  simp[same_ratio],
  apply symm,
end

theorem same_ratio_trans : ∀ p₁ p₂ p₃ : ℤ × ℕ⁺, same_ratio p₁ p₂ → same_ratio p₂ p₃
  → same_ratio p₁ p₃ :=
begin
  intros p₁ p₂ p₃,
  cases p₁ with z₁ n₁,
  cases p₂ with z₂ n₂,
  cases p₃ with z₃ n₃,
  simp[same_ratio],
  intros h₁ h₂,
  apply pos_nat_mul_right_cancel n₂,
  rw [int.mul_assoc,int.mul_comm ↑n₃,← int.mul_assoc,h₁],
  rw [int.mul_assoc,int.mul_comm ↑n₁,← int.mul_assoc,h₂],
  rw [int.mul_assoc,int.mul_assoc,int.mul_comm ↑n₂],
end

instance rational_setoid : setoid (ℤ × ℕ⁺) 
  := ⟨same_ratio,same_ratio_refl,same_ratio_symm,same_ratio_trans⟩

@[simp]
theorem same_ratio_equiv : ∀ (z₁ z₂ : ℤ) (n₁ n₂ : ℕ⁺), (z₁,n₁) ≈ (z₂,n₂) ↔ z₁ * n₂ = z₂ * n₁
  := λ _ _ _ _, by refl

def rational : Type := quotient rational.rational_setoid

notation `ℚ` := rational

instance rational_zero : has_zero ℚ := ⟨⟦(0,1)⟧⟩ 
instance rational_one : has_one ℚ := ⟨⟦(1,1)⟧⟩

theorem rational_zero_concrete_char : (0 : ℚ) = ⟦(0,1)⟧ := rfl
theorem rational_one_concrete_char : (1 : ℚ) = ⟦(1,1)⟧ := rfl

def pre_add_rationals : ℤ × ℕ⁺ → ℤ × ℕ⁺ → ℚ 
| (z₁,n₁) (z₂,n₂) := ⟦(z₁*n₂ + z₂*n₁, n₁ * n₂)⟧

def add_rationals : ℚ → ℚ → ℚ :=
begin
  apply quotient.lift₂ pre_add_rationals,
  intros ap₁ ap₂ bp₁ bp₂ r₁ r₂,
  cases ap₁ with az₁ an₁,
  cases ap₂ with az₂ an₂,
  cases bp₁ with bz₁ bn₁,
  cases bp₂ with bz₂ bn₂,
  simp[pre_add_rationals],
  apply quotient.sound,
  have hrw₁ : az₁ * bn₁ = bz₁ * an₁,
    exact r₁,
  have hrw₂ : az₂ * bn₂ = bz₂ * an₂,
    exact r₂,
  have hrw₃ : (az₁ * ↑an₂ + az₂ * ↑an₁) * ↑(bn₁ * bn₂) 
      = (bz₁ * ↑bn₂ + bz₂ * ↑bn₁) * ↑(an₁ * an₂),
    simp[coe_prevs_mul, int.distrib_right],
    have sub₁ : az₁ * ↑an₂ * (↑bn₁ * ↑bn₂) = bz₁ * ↑bn₂ * (↑an₁ * ↑an₂),
      rw [comm_ring.mul_assoc₄, int.mul_comm ↑an₂,←comm_ring.mul_assoc₄,hrw₁,comm_ring.mul_assoc₄],
      rw [int.mul_assoc,int.mul_comm (↑an₁ * ↑an₂)],
      simp [int.mul_assoc],
    have sub₂ : az₂ * ↑an₁ * (↑bn₁ * ↑bn₂) = bz₂ * ↑bn₁ * (↑an₁ * ↑an₂),
      rw [int.mul_comm ↑bn₁,comm_ring.mul_assoc₄,int.mul_comm ↑an₁,←comm_ring.mul_assoc₄,hrw₂],
      rw [comm_ring.mul_assoc₄,int.mul_comm ↑an₁,int.mul_assoc,int.mul_comm (↑an₂ * ↑an₁)],
      simp [int.mul_assoc],
    rw [sub₁, sub₂],
  exact hrw₃,
end

instance rational_has_add : has_add ℚ := ⟨add_rationals⟩ 

theorem rational_add_concrete_char : ∀ (z₁ z₂ : ℤ) (n₁ n₂ : ℕ⁺), (⟦(z₁,n₁)⟧ + ⟦(z₂,n₂)⟧ : ℚ) =
  ⟦(z₁ * n₂ + z₂ * n₁, n₁ * n₂)⟧ := λ _ _ _ _, rfl

def pre_mul_rationals : ℤ × ℕ⁺ → ℤ × ℕ⁺ → ℚ 
| (z₁,n₁) (z₂,n₂) := ⟦(z₁ * z₂, n₁ * n₂)⟧

def mul_rationals : ℚ → ℚ → ℚ :=
begin
  apply quotient.lift₂ pre_mul_rationals,
  intros ap₁ ap₂ bp₁ bp₂ r₁ r₂,
  cases ap₁ with az₁ an₁,
  cases ap₂ with az₂ an₂,
  cases bp₁ with bz₁ bn₁,
  cases bp₂ with bz₂ bn₂,
  simp[pre_mul_rationals],
  apply quotient.sound,
  have hrw₁ : az₁ * bn₁ = bz₁ * an₁,
    exact r₁,
  have hrw₂ : az₂ * bn₂ = bz₂ * an₂,
    exact r₂,
  have hrw₃ : (az₁ * az₂) * ↑(bn₁ * bn₂) = (bz₁ * bz₂) * ↑(an₁ * an₂),
    simp[coe_prevs_mul],
    rw [comm_ring.mul_assoc₄,int.mul_comm az₂,← comm_ring.mul_assoc₄],
    rw [hrw₁,hrw₂],
    rw [comm_ring.mul_assoc₄, int.mul_comm ↑an₁,← comm_ring.mul_assoc₄],
  exact hrw₃,
end

instance rational_has_mul : has_mul ℚ := ⟨mul_rationals⟩ 

theorem rational_mul_concrete_char : ∀ (z₁ z₂ : ℤ) (n₁ n₂ : ℕ⁺), (⟦(z₁,n₁)⟧ * ⟦(z₂,n₂)⟧ : ℚ) =
  ⟦(z₁ * z₂, n₁ * n₂)⟧ := λ _ _ _ _, rfl

def pre_rational_minus : ℤ × ℕ⁺ → ℚ 
| (z,n) := ⟦(-z,n)⟧

def rational_minus : ℚ → ℚ :=
begin
  apply quotient.lift pre_rational_minus,
  intros p₁ p₂ r,
  cases p₁ with z₁ n₁,
  cases p₂ with z₂ n₂,
  have hrw₁ : z₁ * n₂ = z₂ * n₁,
    exact r,
  apply quotient.sound,
  have hrw₃ : (-z₁) * n₂ = (-z₂) * n₁,
    simp[← comm_ring.minus_mul,hrw₁],
  exact hrw₃,
end

instance rational_has_neg : has_neg ℚ := ⟨rational_minus⟩

theorem rational_minus_concrete_char : ∀ (z : ℤ) (n : ℕ⁺), (-⟦(z,n)⟧ : ℚ) = ⟦(-z,n)⟧ 
  := λ _ _,rfl

instance rational_has_sub : has_sub ℚ := ⟨λ x y, x + -y⟩  

@[simp]
theorem break_down_sub : ∀ x y : ℚ, x - y = x + -y := λ _ _, rfl

end rational