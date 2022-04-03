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

theorem abs_nat : ∀ (n : ℕ) (m : ℕ⁺), abs ⟦(int.of_nat n,m)⟧ = ⟦(int.of_nat n, m)⟧ := λ _ _,rfl

theorem abs_neg : ∀ (n : ℕ) (m : ℕ⁺), abs ⟦(-[1+n],m)⟧ = ⟦(nat.succ n,m)⟧ := λ _ _, rfl

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

theorem ge_zero_abs : ∀ {x : ℚ}, x ≥ 0 → abs x = x :=
begin
  intros x hx,
  cases hx with n hx,
  cases hx with m hx,
  simp[comm_ring.minus_zero_zero, add_zero] at hx,
  simp[hx,abs_nat],
end 

theorem lt_zero_abs : ∀ {x : ℚ}, x < 0 → abs x = -x :=
begin
  intros x hx,
  cases hx with hxless0 nx0,
  cases hxless0 with n hn,
  cases hn with m hxint,
  have hx : x = -⟦(int.of_nat n, m)⟧,
    apply comm_ring.minus_inj,
    rw comm_ring.minus_minus,
    simp[zero_add] at hxint,
    assumption,
  simp[rational_minus_concrete_char] at hx,
  cases n,
  simp[int.of_nat_zero,comm_ring.minus_zero_zero] at hx,
  apply false.elim,
  exact nx0 hx,
  simp [hx,int.neg_of_nat_of_succ,abs_neg,rational_minus_concrete_char],
  simp[← int.neg_of_nat_of_succ,comm_ring.minus_minus],
  refl,
end

lemma ge_or_lt_zero : ∀ x : ℚ, x < 0 ∨ x ≥ 0 :=
begin
  intro x,
  cases le_total x 0,
  cases quotient.exists_rep x with p hp,
  cases p with z m,
  cases z with n n,
  right,
  existsi [n,m],
  simp[hp,comm_ring.minus_zero_zero,add_zero],
  left,
  split,
  existsi [nat.succ n,m],
  simp[← hp,rational_minus_concrete_char,← int.neg_of_nat_of_succ],
  simp[comm_ring.minus_minus,zero_add],
  intro ab,
  rw ab at hp,
  have h₁ := quotient.exact hp,
  simp[int.mul_one,int.zero_mul] at h₁,
  cases h₁,
  right,
  assumption,
end

theorem abs_ge_zero : ∀ x : ℚ, 0 ≤ abs x :=
begin
  intro x,
  cases ge_or_lt_zero x,
  rw lt_zero_abs h,
  cases h,
  cases h_left with n h,
  cases h with m h,
  existsi [n,m],
  simp[comm_ring.minus_zero_zero,add_zero],
  simp[zero_add] at h,
  assumption,
  rw ge_zero_abs h,
  assumption,
end 

theorem le_add_weak : ∀ (b : ℚ) {a₁ a₂ : ℚ}, a₁ ≤ a₂ → a₁ + b ≤ a₂ + b :=
begin
  intros b a₁ a₂ h,
  cases h with n h,
  cases h with m h, 
  existsi [n,m],
  simp[add_comm a₁, comm_ring.minus_dis, comm_ring.add_assoc₄, minus_inverse,add_zero],
  assumption,
end

theorem le_add_weak_iff : ∀ (b : ℚ) {a₁ a₂ : ℚ}, a₁ ≤ a₂ ↔ a₁ + b ≤ a₂ + b :=
begin
  intros b a₁ a₂,
  split,
  apply le_add_weak,
  intro h,
  rw [← add_zero a₁, ← add_zero a₂],
  rw [← minus_inverse b,add_assoc,add_assoc],
  apply le_add_weak (-b),
  assumption,
end

theorem le_add {a₁ a₂ b₁ b₂ : ℚ} : a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + b₁ ≤ a₂ + b₂ :=
begin
  intros ha hb,
  have int₁ : a₁ + b₁ ≤ a₂ + b₁ := le_add_weak b₁ ha,
  have int₂ : a₂ + b₁ ≤ a₂ + b₂, 
    rw add_comm a₂,
    rw add_comm a₂,
    exact le_add_weak a₂ hb,
  apply le_trans,
  assumption,
  assumption,
end

theorem abs_upper_bound : ∀ x : ℚ, x ≤ abs x ∧ -x ≤ abs x :=
begin
  intro x,
  cases ge_or_lt_zero x,
  split,
  cases h,
  apply le_trans,
  assumption,
  apply abs_ge_zero,
  rw lt_zero_abs h,
  apply le_refl,
  split,
  rw ge_zero_abs h,
  apply le_refl,
  apply le_trans,
  have int : -x ≤ 0,
    cases h with n h,
    cases h with m h,
    existsi [n, m],
    simp[comm_ring.minus_minus,zero_add],
    simp[comm_ring.minus_zero_zero,add_zero] at h,
    assumption,
  assumption,
  apply abs_ge_zero,
end

theorem abs_minus : ∀ x : ℚ, abs (-x) = abs x :=
begin
  intro,
  cases quotient.exists_rep x with p hp,
  cases p with z n,
  simp[← hp,rational_minus_concrete_char],
  cases z with m m,
  cases m,
  simp[comm_ring.minus_zero_zero,int.of_nat_zero],
  simp[int.neg_of_nat_of_succ,abs_neg,abs_nat],
  refl,
  simp[← int.neg_of_nat_of_succ,abs_neg,abs_nat,comm_ring.minus_minus],
  simp[int.neg_of_nat_of_succ,abs_neg],
  refl,
end

theorem triangle_inequality : ∀ x y : ℚ, abs (x + y) ≤ abs x + abs y := 
begin
  intros x y,
  cases ge_or_lt_zero (x + y),
  rw [lt_zero_abs h, comm_ring.minus_dis],
  apply le_add,
  exact (abs_upper_bound x).2,
  exact (abs_upper_bound y).2,
  rw ge_zero_abs h,
  apply le_add,
  exact (abs_upper_bound x).1,
  exact (abs_upper_bound y).1,
end

theorem scale_pos_rat {ε : ℚ} {n : ℕ} {m : ℕ⁺} (k : ℕ⁺) : (0 ≠ ε) → (ε = ⟦(int.of_nat n,m)⟧)
  → let ε' : ℚ := ⟦(int.of_nat n,m*k)⟧ in ε' > 0 :=
begin
  intros nε hε,
  simp,
  split,
  existsi [n, m*k],
  simp[add_zero, comm_ring.minus_zero_zero],
  intro ab,
  have hcon := quotient.exact ab,
  simp[int.zero_mul,int.mul_one] at hcon,
  rw ← hcon at hε,
  simp at hε,
  apply nε,
  symmetry,
  assumption,
end

theorem lt_not_ge : ∀ x y : ℚ , x < y ↔ ¬(x ≥ y) :=
begin
  intros x y,
  split,
  intros hxy hyx,
  cases hxy with hxy nxy,
  apply nxy,
  apply le_antisymm,
  assumption,
  assumption,
  intro h,
  cases le_total x y with h₁,
  split,
  assumption,
  intro ab,
  rw ab at h,
  apply h,
  apply le_refl,
  apply false.elim,
  apply h,
  assumption, 
end


theorem lt_trans : ∀ {x y z : ℚ} , x < y → y < z → x < z :=
begin
  intros x y z h₁ h₂,
  rw lt_not_ge,
  intro ab,
  cases h₁ with lxy exy,
  cases h₂ with lyz eyz,
  apply exy,
  apply le_antisymm,
  assumption,
  apply le_trans,
  apply le_trans,
  assumption,
  assumption,
  apply le_refl,
end

theorem lt_add_weak : ∀ (b : ℚ) {a₁ a₂ : ℚ}, a₁ < a₂ → a₁ + b < a₂ + b :=
begin
  intros b a₁ a₂ h12,
  cases h12 with l12 e12,
  rw lt_not_ge,
  intro ab,
  apply e12,
  apply le_antisymm,
  assumption,
  rw le_add_weak_iff,
  assumption,
end

theorem lt_add {a₁ a₂ b₁ b₂ : ℚ} : a₁ < a₂ → b₁ < b₂ → a₁ + b₁ < a₂ + b₂ :=
begin
  intros ha hb,
  have int₁ : a₁ + b₁ < a₂ + b₁ := lt_add_weak b₁ ha,
  have int₂ : a₂ + b₁ < a₂ + b₂, 
    rw add_comm a₂,
    rw add_comm a₂,
    exact lt_add_weak a₂ hb,
  apply lt_trans,
  assumption,
  assumption,
end

theorem le_then_lt_lt {a₁ a₂ a₃ : ℚ} : a₁ ≤ a₂ → a₂ < a₃ → a₁ < a₃ :=
begin
  intros l12 h23,
  cases h23 with l23 n23,
  rw lt_not_ge,
  intro l31,
  apply n23,
  apply le_antisymm,
  assumption,
  apply le_trans,
  assumption,
  assumption,
end

end rational