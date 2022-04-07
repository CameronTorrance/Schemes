import misc.rationals.basic


namespace rational

theorem add_zero : ∀ r : ℚ, r + 0 = r :=
begin
  intro r,
  cases quotient.exists_rep r with p hp,
  cases p with z n, 
  rw [← hp,rational_zero_concrete_char,rational_add_concrete_char],
  have trv : n * 1 = n,
    apply coe_inj,
    simp[int.mul_one],
  simp[int.zero_mul,int.add_zero,int.mul_one, trv],
end

theorem zero_add : ∀ r : ℚ, 0 + r = r :=
begin
  intro r,
  cases quotient.exists_rep r with p hp,
  cases p with z n, 
  simp [← hp,rational_zero_concrete_char,rational_add_concrete_char],
  simp[int.zero_mul,int.zero_add,int.mul_one],
  refl,
end

theorem mul_one : ∀ r : ℚ, r * 1 = r :=
begin
  intro r,
  cases quotient.exists_rep r with p hp,
  cases p with z n, 
  rw [← hp,rational_one_concrete_char,rational_mul_concrete_char],
  have trv : n * 1 = n,
    apply coe_inj,
    simp[int.mul_one],
  simp[int.mul_one,trv],
end

theorem one_mul : ∀ r : ℚ, 1 * r = r :=
begin
  intro r,
  cases quotient.exists_rep r with p hp,
  cases p with z n, 
  simp [← hp,rational_one_concrete_char,rational_mul_concrete_char],
  simp[int.one_mul],
  refl,
end

theorem mul_comm : ∀ r₁ r₂ : ℚ, r₁ * r₂ = r₂ * r₁ :=
begin
  intros r₁ r₂,
  cases quotient.exists_rep r₁ with p₁ hp₁,
  cases p₁ with z₁ n₁,
  cases quotient.exists_rep r₂ with p₂ hp₂,
  cases p₂ with z₂ n₂,
  have trv : n₁ * n₂ = n₂ * n₁,
    apply coe_inj,
    simp[int.mul_comm],
  simp[←hp₁,←hp₂,trv,rational_mul_concrete_char,int.mul_comm],
end

theorem mul_assoc : ∀ r₁ r₂ r₃ : ℚ, r₁ * (r₂ * r₃) = (r₁ * r₂) * r₃ :=
begin
  intros r₁ r₂ r₃,
  cases quotient.exists_rep r₁ with p₁ hp₁,
  cases p₁ with z₁ n₁,
  cases quotient.exists_rep r₂ with p₂ hp₂,
  cases p₂ with z₂ n₂,
  cases quotient.exists_rep r₃ with p₃ hp₃,
  cases p₃ with z₃ n₃,
  simp[← hp₁,← hp₂,← hp₃,rational_mul_concrete_char],
  have trv : n₁ * (n₂ * n₃) = (n₁ * n₂) * n₃,
    apply coe_inj,
    simp[int.mul_assoc],
  simp[trv,int.mul_assoc],
end

theorem add_comm : ∀ r₁ r₂ : ℚ, r₁ + r₂ = r₂ + r₁ :=
begin
  intros r₁ r₂,
  cases quotient.exists_rep r₁ with p₁ hp₁,
  cases p₁ with z₁ n₁,
  cases quotient.exists_rep r₂ with p₂ hp₂,
  cases p₂ with z₂ n₂,
  have trv : n₁ * n₂ = n₂ * n₁,
    apply coe_inj,
    simp[int.mul_comm],
  simp[←hp₁,←hp₂,trv,rational_add_concrete_char,int.add_comm],
end

theorem add_assoc : ∀ r₁ r₂ r₃ : ℚ, r₁ + (r₂ + r₃) = (r₁ + r₂) + r₃ :=
begin
  intros r₁ r₂ r₃,
  cases quotient.exists_rep r₁ with p₁ hp₁,
  cases p₁ with z₁ n₁,
  cases quotient.exists_rep r₂ with p₂ hp₂,
  cases p₂ with z₂ n₂,
  cases quotient.exists_rep r₃ with p₃ hp₃,
  cases p₃ with z₃ n₃,
  simp[← hp₁,← hp₂,← hp₃,rational_add_concrete_char],
  have trv : n₁ * (n₂ * n₃) = (n₁ * n₂) * n₃,
    apply coe_inj,
    simp[int.mul_assoc],
  simp[trv,int.add_assoc,int.mul_assoc,int.distrib_right],
  simp[int.mul_comm],
end

theorem fraction_cancel : ∀ (n m : ℕ⁺) (z : ℤ), ⟦(z * m,n * m)⟧ = ⟦(z,n)⟧ :=
begin
  intros n m z,
  apply quotient.sound,
  have res : (z * ↑m) * ↑n = z * ↑(n * m),
    simp[int.mul_comm ↑n,int.mul_assoc],
  exact res,
end

theorem mul_dis : ∀ r₁ r₂ r₃ : ℚ, r₁ * (r₂ + r₃) = (r₁ * r₂) + (r₁ * r₃) :=
begin
  intros r₁ r₂ r₃,
  cases quotient.exists_rep r₁ with p₁ hp₁,
  cases p₁ with z₁ n₁,
  cases quotient.exists_rep r₂ with p₂ hp₂,
  cases p₂ with z₂ n₂,
  cases quotient.exists_rep r₃ with p₃ hp₃,
  cases p₃ with z₃ n₃,
  simp[← hp₁,← hp₂,← hp₃,rational_add_concrete_char,rational_mul_concrete_char],
  have hrw₁ : z₁ * z₂ * (↑n₁ * ↑n₃) = z₁ * (z₂ * ↑n₃) * n₁,
    rw int.mul_comm ↑n₁,
    rw comm_ring.mul_assoc₄,
  have hrw₂ : z₁ * z₃ * (↑n₁ * ↑n₂) = z₁ * (z₃ * ↑n₂) * n₁,
    rw int.mul_comm ↑n₁,
    rw comm_ring.mul_assoc₄,
  have hrw₃ : n₁ * n₂ * (n₁ * n₃) = n₁ * (n₂ * n₃) * n₁,
    apply coe_inj,
    simp[int.mul_comm n₁ n₃,comm_ring.mul_assoc₄],
  rw [hrw₁,hrw₂,hrw₃,← int.distrib_right,fraction_cancel,int.distrib_left],
end

theorem minus_inverse : ∀ a : ℚ , a + (-a) = 0 :=
begin
  intro r,
  cases quotient.exists_rep r with p hp,
  cases p with z n,
  simp[←hp,rational_add_concrete_char,rational_minus_concrete_char],
  rw [← int.distrib_right,int.add_right_neg,int.zero_mul],
  apply quotient.sound,
  have res : (0 * 1:ℤ) = 0 * ↑(n * n) := by simp[int.zero_mul],
  exact res,
end

instance rational_comm_ring : comm_ring ℚ :=
{
  add_assoc := add_assoc,
  mul_assoc := mul_assoc,
  mul_dis   := mul_dis,
  add_comm := add_comm,
  mul_comm := mul_comm,
  add_zero := add_zero,
  mul_one := mul_one,
  minus_inverse := minus_inverse,
}

theorem sub_antisymm : ∀ x y : ℚ, x - y = -(y - x) :=
begin
  intros x y,
  simp[comm_ring.minus_dis,comm_ring.minus_minus,add_comm],
end 

@[simp] 
theorem better_zero_concrete_char : ∀ n : ℕ⁺, ⟦((0:ℤ),n)⟧ = (0: ℚ) :=
begin
  intro,
  apply quotient.sound,
  simp[int.zero_mul],
end

lemma mul_two_div_rat_by_two : ∀ (n : ℕ) (m : ℕ⁺), ⟦(int.of_nat n, m)⟧ = 
  (⟦(int.of_nat n, m*2)⟧ + ⟦(int.of_nat n, m*2)⟧ : ℚ) :=
begin
  intros n m,
  rw [rational_add_concrete_char,← int.distrib_right],
  rw fraction_cancel,
  have hrw : int.of_nat n + int.of_nat n = (int.of_nat n) * ↑(2:ℕ⁺),
    have sub₁ : ↑(2:ℕ⁺) = (2:ℤ) := rfl,
    rw sub₁,
    rw int.mul_comm,
    have sub₂ : 2 = int.of_nat 2 := rfl, 
    simp[← int.of_nat_add,sub₂,← int.of_nat_mul,nat.succ_mul,nat.zero_mul,nat.zero_add],
    rw [hrw,fraction_cancel],
end


end rational