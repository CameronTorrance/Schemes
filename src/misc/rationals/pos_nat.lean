import algebra.comm_rings.instances.basic

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

theorem pos_nat_mul_suc : ∀ n m : ℕ⁺, (pos_nat.succ n) * m = m + (n * m) := λ _ _, rfl

theorem pos_nat.one_mul : ∀ n : ℕ⁺, pos_nat.one * n = n := λ _,rfl
theorem pos_nat.one_mul₁ : ∀ n : ℕ⁺ , 1 * n = n := λ _, rfl

def pos_nat_to_nat : ℕ⁺ → ℕ 
| pos_nat.one      := 1
| (pos_nat.succ k) := nat.succ (pos_nat_to_nat k) 

def pot_nat_to_int :  ℕ⁺ → ℤ 
| 1       := int.of_nat 1 
| (1 + n) := 1 + pot_nat_to_int n 

theorem pos_nat_to_nat_never_zero : ∀ n : ℕ⁺, pos_nat_to_nat n ≠ 0 :=
begin
  intros n ab,
  cases n with n,
  cases ab,
  cases ab,
end

theorem pos_nat_to_nat_inj : ∀ {n₁ n₂ : ℕ⁺}, pos_nat_to_nat n₁ = pos_nat_to_nat n₂ → n₁ = n₂ 
| pos_nat.one pos_nat.one _ := rfl
| (pos_nat.succ n) pos_nat.one h := 
  begin
    apply false.elim,
    apply pos_nat_to_nat_never_zero n,
    apply nat.succ.inj,
    assumption,
  end
| pos_nat.one (pos_nat.succ n) h :=
  begin
    apply false.elim,
    apply pos_nat_to_nat_never_zero n,
    apply nat.succ.inj,
    symmetry,
    assumption,
  end
| (pos_nat.succ n₁) (pos_nat.succ n₂) h :=
  begin
    have hrw : n₁ = n₂,
      apply pos_nat_to_nat_inj,
      apply nat.succ.inj,
      assumption,
    rw hrw,
  end

instance pos_nat_coe : has_coe ℕ⁺ ℤ := ⟨pot_nat_to_int⟩

@[simp]
theorem coe_pos_one : ↑(pos_nat.one) = (1:ℤ) := rfl

@[simp]
theorem coe_pos_one₁ : ↑(1:ℕ⁺) = (1:ℤ) := rfl

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

theorem strong_pos_nat_nat_coor : ∀ n : ℕ⁺, ↑n = int.of_nat (pos_nat_to_nat n) :=
begin
  intro n,
  induction n with n hn,
  refl,
  simp[hn],
  have trv : pos_nat_to_nat n.succ = (pos_nat_to_nat n).succ := rfl, 
  simp [trv,int.of_nat_succ,int.add_comm],
end

@[simp]
theorem coe_prevs_add : ∀ n₁ n₂ : ℕ⁺, (↑(n₁ + n₂) : ℤ) = ↑n₁ + ↑n₂ :=
begin
  intros n₁ n₂,
  induction n₁ with n₁ hn₁,
  have trv : pos_nat.one + n₂ = n₂.succ := rfl,
  simp[trv],
  have trv : n₁.succ + n₂ = (n₁ + n₂).succ := rfl,
  simp[trv,hn₁,int.add_assoc],
end

@[simp]
theorem coe_prevs_mul : ∀ n₁ n₂ : ℕ⁺, (↑(n₁ * n₂) : ℤ) = ↑n₁ * ↑n₂ :=
begin
  intros n₁ n₂,
  induction n₁ with n₁ hn₁,
  simp [pos_nat.one_mul, int.one_mul],
  simp[int.distrib_right, int.one_mul],
  have trv : n₁.succ * n₂ = n₂ + n₁ * n₂ := rfl,
  simp[trv,coe_prevs_add, hn₁],
end

theorem coe_inj : ∀ n₁ n₂ : ℕ⁺, (↑n₁ : ℤ) = ↑n₂ → n₁ = n₂ :=
begin
  intros n₁ n₂,
  simp[strong_pos_nat_nat_coor],
  intro h,
  apply pos_nat_to_nat_inj,
  assumption,
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