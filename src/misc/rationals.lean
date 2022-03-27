import algebra.comm_rings.instances.basic

namespace rational

inductive pos_nat 
| one  : pos_nat
| succ : pos_nat → pos_nat

notation `ℕ⁺` := pos_nat

def pos_nat_add : ℕ⁺ → ℕ⁺ → ℕ⁺ 
| pos_nat.one n      := pos_nat.succ n
| (pos_nat.succ k) n := pos_nat.succ (pos_nat_add k n)

instance pos_nat_has_one : has_one ℕ⁺ := ⟨pos_nat.one⟩
instance pos_nat_has_add : has_add ℕ⁺ := ⟨pos_nat_add⟩   

def pos_nat_mul : ℕ⁺ → ℕ⁺ → ℕ⁺ 
| (1:ℕ⁺) n           := n
| (pos_nat.succ k) n := n + (pos_nat_mul k n)

instance pos_nat_has_mul : has_mul ℕ⁺ := ⟨pos_nat_mul⟩

theorem pos_nat.one_mul : ∀ n : ℕ⁺, pos_nat.one * n = n := λ _,rfl

def pot_nat_to_int :  ℕ⁺ → ℤ 
| 1       := int.of_nat 1 
| (1 + n) := 1 + pot_nat_to_int n 

instance pos_nat_coe : has_coe ℕ⁺ ℤ := ⟨pot_nat_to_int⟩

@[simp]
theorem coe_pos_one : ↑(pos_nat.one) = (1:ℤ) := rfl

@[simp]
theorem coe_pos_suc : ∀ n : ℕ⁺, ↑(pos_nat.succ n) = (1 + ↑n : ℤ) := λ _, rfl

theorem pos_nat_nat_coor : ∀ n : ℕ⁺, ∃ m : ℕ, ↑n = int.of_nat m :=
begin
  intro n,
  induction n with n hn,
  existsi 1,
  refl,
  cases hn with m hm,
  existsi nat.succ m,
  simp[hm,int.of_nat_succ,int.add_comm],
end

theorem coe_prevs_add : ∀ n₁ n₂ : ℕ⁺, (↑(n₁ + n₂) : ℤ) = ↑n₁ + ↑n₂ :=
begin
  intros n₁ n₂,
  induction n₁ with n₁ hn₁,
  have trv : pos_nat.one + n₂ = n₂.succ := rfl,
  simp[trv],
  have trv : n₁.succ + n₂ = (n₁ + n₂).succ := rfl,
  simp[trv,hn₁,int.add_assoc],
end

theorem coe_prevs_mul : ∀ n₁ n₂ : ℕ⁺, (↑(n₁ * n₂) : ℤ) = ↑n₁ * ↑n₂ :=
begin
  intros n₁ n₂,
  induction n₁ with n₁ hn₁,
  simp [pos_nat.one_mul, int.one_mul],
  simp[int.distrib_right, int.one_mul],
  have trv : n₁.succ * n₂ = n₂ + n₁ * n₂ := rfl,
  simp[trv,coe_prevs_add, hn₁],
end

theorem mul_zero_eq_zero : ∀ {z : ℤ} (n : ℕ⁺), z * n = 0 → z = 0 :=
begin
  intros z n h,
  cases z with m m,
  cases m,
  refl,
  apply false.elim,
  rw int.of_nat_succ at h,
  rw int.distrib_right at h,
  rw int.one_mul at h,
  cases n,
  simp[int.mul_one] at h,
  rw ← int.of_nat_succ at h,
  cases h,
  cases pos_nat_nat_coor n with c hc,
  simp [hc,int.distrib_left,int.mul_one] at h,
  rw [← int.of_nat_mul, ← int.of_nat_add, int.add_comm 1] at h,
  rw [← int.add_assoc,← int.of_nat_add,← int.of_nat_succ] at h,
  cases h,
  cases n,
  simp[int.mul_one] at h,
  assumption,
  simp[int.distrib_left] at h,
  rw int.mul_one at h,
  cases pos_nat_nat_coor n with c hc,
  simp[hc] at h,
  have hrw : -[1+ m] * int.of_nat c = int.neg_of_nat (nat.succ m * c) := rfl,
  rw hrw at h, 
  cases c,
  rw nat.mul_zero m.succ at h,
  simp[int.neg_of_nat,int.add_zero] at h,
  assumption,
  simp [nat.mul_succ,nat.add_succ,int.neg_of_nat] at h,
  have trv : ∀ m₁ m₂,  -[1+ m₁] + -[1+ m₂] = -[1+ nat.succ (m₁ + m₂)] := λ _ _, rfl,
  simp[trv] at h,
  apply false.elim,
  cases h,
end 

lemma pos_nat_mul_right_cancel : ∀ {z₁ z₂: ℤ} (n : ℕ⁺), z₁ * n = z₂ * n  → z₁ = z₂ :=
begin
  intros z₁ z₂ n h,
  have hrw : z₁ + -z₂ = 0,
    apply mul_zero_eq_zero n,
    rw [int.distrib_right, h,← comm_ring.minus_mul],
    rw comm_ring.minus_inverse,
    exact calc z₁ = z₁ + 0          : by rw int.add_zero z₁
              ... = z₁ + (z₂ + -z₂) : by rw comm_ring.minus_inverse
              ... = z₁ + (-z₂ + z₂) : by rw int.add_comm z₂
              ... = (z₁ + -z₂) + z₂ : by simp[int.add_assoc]
              ... = 0 + z₂          : by rw hrw
              ... = z₂              : by rw int.zero_add,
end

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

def rational : Type := quotient rational.rational_setoid

notation `ℚ` := rational

instance rational_zero : has_zero ℚ := ⟨⟦(0,1)⟧⟩ 
instance rational_one : has_one ℚ := ⟨⟦(1,1)⟧⟩

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
instance rational_has_sub : has_sub ℚ := ⟨λ x y, x + -y⟩  

theorem rational_minus_concrete_char : ∀ (z : ℤ) (n : ℕ⁺), (-⟦(z,n)⟧ : ℚ) = ⟦(-z,n)⟧ := λ _ _, rfl

def pre_le_rational : ℤ × ℕ⁺ → ℤ × ℕ⁺ → Prop
| (z₁,n₁) (z₂,n₂) := z₁ * n₂ ≤ z₂ * n₁

def le_rational : ℚ → ℚ → Prop :=
begin
  apply quotient.lift₂ pre_le_rational,
  intros ap₁ ap₂ bp₁ bp₂ r₁ r₂,
  cases ap₁ with az₁ an₁,
  cases ap₂ with az₂ an₂,
  cases bp₁ with bz₁ bn₁,
  cases bp₂ with bz₂ bn₂, 
  have hrw₁ : az₁ * bn₁ = bz₁ * an₁,
    exact r₁,
  have hrw₂ : az₂ * bn₂ = bz₂ * an₂,
    exact r₂,
    simp[pre_le_rational],
    sorry,
end

instance rational_has_le : has_le ℚ := ⟨le_rational⟩ 


end rational