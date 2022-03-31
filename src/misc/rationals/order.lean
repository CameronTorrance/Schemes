import misc.rationals.basic
import misc.rationals.alg_props

open classical

namespace rational

def pre_abs : ℤ × ℕ⁺ → ℚ
| (int.of_nat n,m) := ⟦(int.of_nat n,m)⟧
| (-[1+n],m)       := ⟦(nat.succ n,m)⟧

def abs : ℚ → ℚ :=
begin
  apply quotient.lift pre_abs,
  intros p₁ p₂ h,
  cases p₁ with z₁ m₁,
  cases z₁ with n₁ n₁,
  cases p₂ with z₂ m₂,
  cases z₂ with n₂ n₂,
  simp[pre_abs],
  exact quotient.sound h,
  simp[pre_abs],
  simp[strong_pos_nat_nat_coor, ← int.of_nat_mul] at h,
  have trv : -[1+ n₂] * int.of_nat (pos_nat_to_nat m₁) 
    = int.neg_of_nat (nat.succ n₂ * (pos_nat_to_nat m₁)) := rfl,
  rw [trv,nat.succ_mul] at h,
  cases m₁,
  simp [nat.add_succ,pos_nat_to_nat,int.neg_of_nat] at h,
  cases h,
  simp [nat.add_succ,pos_nat_to_nat,int.neg_of_nat] at h,
  cases h,
  cases p₂ with z₂ m₂,
  cases z₂ with n₂ n₂,
  have trv : -[1+ n₁] * int.of_nat (pos_nat_to_nat m₂) 
    = int.neg_of_nat (nat.succ n₁ * (pos_nat_to_nat m₂)) := rfl,
  simp[trv,strong_pos_nat_nat_coor, ← int.of_nat_mul] at h,
  cases m₂,
  simp [nat.add_succ,nat.mul_one,pos_nat_to_nat,int.neg_of_nat] at h,
  cases h,
  simp [nat.add_succ,nat.mul_one,pos_nat_to_nat,int.neg_of_nat] at h,
  cases h,
  simp[pre_abs],
  apply quotient.sound,
  simp at h,
  have trv₁ : -[1+ n₂] * int.of_nat (pos_nat_to_nat m₁) 
    = int.neg_of_nat (nat.succ n₂ * (pos_nat_to_nat m₁)) := rfl,
  have trv₂ : -[1+ n₁] * int.of_nat (pos_nat_to_nat m₂) 
    = int.neg_of_nat (nat.succ n₁ * (pos_nat_to_nat m₂)) := rfl,
  simp[trv₁,trv₂,strong_pos_nat_nat_coor] at h,
  have h₁ : -int.neg_of_nat (n₁.succ * pos_nat_to_nat m₂) = 
    -int.neg_of_nat (n₂.succ * pos_nat_to_nat m₁),
    rw h,
  have trv₃ : ∀ n : ℕ, -(int.of_nat n) = int.neg_of_nat n,
    intro,
    refl,
  have trv₄ : ∀ n : ℕ, ↑n = int.of_nat n := λ _, rfl,
  simp [← trv₃,comm_ring.minus_minus] at h₁,
  simp,
  simp [trv₄,strong_pos_nat_nat_coor,← int.of_nat_mul],
  assumption,
end

theorem abs_zero : abs 0 = 0 := rfl 

theorem abs_nat : ∀ (n : ℕ) (m : ℕ⁺) , abs ⟦(int.of_nat n,m)⟧ = ⟦(int.of_nat n, m)⟧ := λ _ _,rfl

def rational_le (x y: ℚ) : Prop := ∃ (n : ℕ) (m : ℕ⁺), y - x = ⟦(int.of_nat n, m)⟧

instance rationals_ordered : has_le ℚ := ⟨rational_le⟩ 
instance rationals_lt      : has_lt ℚ := ⟨λ x y : ℚ, x ≤ y ∧ x ≠ y⟩ 

@[simp]
theorem rational_le_defn : ∀ x y : ℚ, x ≤ y ↔ ∃ (n : ℕ) (m : ℕ⁺), y - x = ⟦(int.of_nat n, m)⟧ :=
begin
  intros x y,
  refl,
end

theorem le_refl : ∀ x : ℚ, x ≤ x :=
begin
  intro x,
  simp,
  existsi [0,(1: ℕ⁺)],
  rw minus_inverse,
  refl,
end

theorem le_trans : ∀ x y z : ℚ, x ≤ y → y ≤ z → x ≤ z :=
begin
  simp,
  intros x y z hxy hyz,
  cases hxy with nxy hxy,
  cases hxy with mxy hxy,
  cases hyz with nyz hyz,
  cases hyz with myz hyz,
  existsi[nxy * (pos_nat_to_nat myz) + nyz * (pos_nat_to_nat mxy), mxy * myz],
  simp [int.of_nat_add,int.of_nat_mul,← strong_pos_nat_nat_coor],
  rw [← rational_add_concrete_char,← hxy,← hyz],
  rw [add_comm y,add_comm z,add_comm z, comm_ring.add_assoc₄,minus_inverse,add_zero],
end

lemma minus_of_nat_eq : ∀ {n m : ℕ}, -int.of_nat n = int.of_nat m → n = 0 :=
begin
  intros n m eq,
  induction n with n hn,
  refl,
  rw int.neg_of_nat_of_succ at eq,
  cases eq,
end

theorem le_antisymm : ∀ x y : ℚ, x ≤ y → y ≤ x → x = y :=
begin
  intros x y hxy hyx,
  cases hxy with nxy hxy,
  cases hxy with mxy hxy,
  cases hyx with nyx hyx,
  cases hyx with myx hyx,
  rw sub_antisymm at hyx,
  rw [hxy,rational_minus_concrete_char] at hyx,
  have arg := quotient.exact hyx,
  simp[strong_pos_nat_nat_coor,← int.of_nat_mul,← comm_ring.minus_mul] at arg,
  have arg₁ : nxy * pos_nat_to_nat myx = 0,
    apply minus_of_nat_eq,
    assumption,
  have arg₂ : nxy = 0,
    apply int.of_nat.inj,
    apply pos_nat_mul_right_cancel myx,
    simp[strong_pos_nat_nat_coor,←int.of_nat_mul,nat.zero_mul],
    assumption,
  simp[arg₂] at hxy,
  symmetry,
  apply comm_ring.zero_diff_equal,
  rw hxy,
  simp[int.of_nat_zero],
end

theorem le_total : ∀ x y : ℚ , x ≤ y ∨ y ≤ x :=
begin
  intros x y,
  cases quotient.exists_rep (y - x : ℚ) with p hp,
  cases p with z m,
  cases z with n n,
  simp,
  left,
  existsi [n,m],
  symmetry,
  assumption,
  right,
  existsi [n.succ,m],
  apply comm_ring.minus_inj,
  rw [sub_antisymm,comm_ring.minus_minus,rational_minus_concrete_char],
  rw int.neg_of_nat_of_succ,
  symmetry,
  assumption,
end

end rational