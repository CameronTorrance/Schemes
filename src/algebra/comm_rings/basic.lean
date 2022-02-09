namespace comm_ring

universes u v w

open list

class comm_ring (R: Type u) extends has_add R, has_mul R, has_one R, has_zero R, has_neg R :=
  (add_assoc : ∀ a b c : R, a + (b + c) = (a + b) + c)
  (add_comm : ∀ a b : R, a + b = b + a)
  (add_zero : ∀ a : R, a + 0 = a)
  (minus_inverse : ∀ a : R, a + (-a) = 0)
  (mul_assoc : ∀ a b c : R, a * (b * c) = (a * b) * c)
  (mul_comm : ∀ a b : R, a * b = b * a)
  (mul_one : ∀ a : R, a * 1 = a)
  (mul_dis : ∀ a b c : R, a * (b + c) = a * b + a * c)

theorem add_assoc {R: Type u} [l : comm_ring R] : ∀ a b c : R, a + (b + c) = (a + b) + c := l.add_assoc
theorem add_comm {R: Type u} [l: comm_ring R] : ∀ a b : R, a + b = b + a := l.add_comm
theorem add_zero {R: Type u} [l: comm_ring R] : ∀ a : R, a + 0 = a := l.add_zero
theorem minus_inverse {R: Type u} [l: comm_ring R] : ∀ a : R, a + -a = 0 := l.minus_inverse
theorem mul_assoc {R: Type u} [l: comm_ring R] : ∀ a b c : R, a * (b * c) = (a * b) * c := l.mul_assoc
theorem mul_comm {R: Type u} [l: comm_ring R] : ∀ a b : R, a * b = b * a := l.mul_comm
theorem mul_one {R: Type u} [l: comm_ring R] : ∀ a : R, a * 1 = a := l.mul_one
theorem mul_dis {R: Type u} [l: comm_ring R] : ∀ a b c : R, a * (b + c) = a * b + a * c := l.mul_dis 

/-
  Trival algebraic identities. 
-/

def unit {R: Type u} [comm_ring R] (x : R) : Prop := ∃ a : R,  a * x = 1

theorem one_is_unit {R: Type u} [l:comm_ring R] : unit l.one := 
begin
  existsi l.one,
  rw mul_one,
end

theorem zero_unquie {R: Type u} [comm_ring R] : ∀ a : R, (∀ b : R, b + a = b) → a = 0 :=
begin
  intros a h,
  exact calc a = a + 0 : by rw add_zero
        ...    = 0 + a : by rw add_comm
        ...    = 0      : h 0
end

theorem one_unquie {R: Type u} [comm_ring R] : ∀ a : R, (∀ b : R, b * a = b) → a = 1 :=
begin
  intros a h,
  exact calc a = a * 1 : by rw mul_one
        ...    = 1 * a : by rw mul_comm
        ...    = 1      : h 1
end

theorem minus_unquie {R: Type u} [comm_ring R] : ∀ a b : R, a + b = 0 → b = -a :=
begin
  intros a b h,
  rw ← minus_inverse a at h,
  exact calc b = b + 0          : by rw  add_zero b
           ... = b + (a + (-a)) : by rw ← minus_inverse a
           ... = (b + a) + -a   : by rw add_assoc
           ... = (a + b) + -a   : by rw add_comm a b
           ... = (a + -a) + -a  : by rw ← h
           ... = (-a + a) + -a  : by simp [add_comm]
           ... = -a + 0         : by rw [← add_assoc,minus_inverse]
           ... = -a             : add_zero (-a)
end

theorem mul_zero {R : Type u} [l:comm_ring R] : ∀ a : R, a * 0 = 0 := 
begin
  intro a,
  have sub : (a * 0) + (a * 0) = a * 0,
  simp [←mul_dis,add_zero],
  exact calc a * 0 = (a * 0 + a * 0) + -(a * 0) : by simp [add_zero,minus_inverse,←add_assoc]
               ... = 0                          : by simp [sub,minus_inverse]
end

theorem mul_minus_one {R : Type u} [comm_ring R] : ∀ a : R, a * (-1) = -a :=
begin
  intro a,
  apply minus_unquie,
  exact calc a + a * -1 = a * (1 + (-1)) : by simp [mul_one,mul_dis]
                    ... = 0              : by simp [minus_inverse,mul_zero], 
end

theorem minus_dis {R : Type u} [comm_ring R] : ∀ a b : R , -(a + b) = -a + -b :=
begin
  intros a b,
  symmetry,
  apply minus_unquie,
  exact calc (a + b) + (-a + -b) = a + (b + -a) + -b   : by simp [add_assoc]
                             ... = (a + -a) + (b + -b) : by {rw add_comm b (-a), simp [add_assoc]}
                             ... = 0                   : by rw [minus_inverse,minus_inverse,add_zero], 
end

theorem minus_zero_zero {R : Type u} [l:comm_ring R] : -l.zero = l.zero :=
begin
  symmetry,
  apply minus_unquie,
  exact add_zero 0,
end

theorem minus_mul {R : Type u} [comm_ring R] : ∀ a b : R, -(a * b) = (-a) * b :=
begin
  intros a b,
  symmetry,
  apply minus_unquie,
  rw [mul_comm a b,mul_comm (-a) b,← mul_dis,minus_inverse,mul_zero],
end

theorem minus_minus {R : Type u} [comm_ring R] : ∀ x : R , -(-x) = x :=
begin
  intro x,
  symmetry,
  apply minus_unquie,
  rw add_comm,
  rw minus_inverse,
end 

def pow {R : Type u} [comm_ring R] : R → ℕ → R 
  | r nat.zero     := 1
  | r (nat.succ n) := r * (pow r n)

infixr `^` := pow

def nat_to_ring (R :Type u) [comm_ring R] : ℕ → R 
  | 0            := 0
  | (nat.succ n) := 1 + nat_to_ring n 

def binomial_coeffients : ℕ → ℕ → ℕ
  | _ 0                       := 1
  | 0 _                       := 1
  | (nat.succ n) (nat.succ k) := (binomial_coeffients n (nat.succ k)) + (binomial_coeffients n k)


def sum_list {R : Type u} [comm_ring R] : list R → R := foldr (λ a b : R, a + b) 0

def scale_list {R : Type u} [comm_ring R] : R → list R → list R := λ a, map (λ b: R, a * b)

def add_lists {R : Type u} [comm_ring R] : list R → list R → list R 
  | (a :: as) (b :: bs) := (a + b) :: (add_lists as bs)
  | [] bs               := bs 
  | as []               := as 

notation `Σ₀` : 110 := sum_list

theorem mul_dis_general {R : Type u} [comm_ring R] : ∀ (a : R) (l : list R), a * (Σ₀ l) = Σ₀ (scale_list a l) :=
begin
  intros a l,
  induction l with b l hl,
  have trv₁ : (Σ₀ (@nil R)) = 0 := rfl,
  have trv₂ : scale_list a nil = nil := rfl,
  rw [trv₂,trv₁,mul_zero],
  have trv₁ : Σ₀ (b::l) = b + Σ₀ l := rfl,
  rw [trv₁,mul_dis,hl],
  refl, 
end


inductive linear_combination {R : Type u} [comm_ring R] (S₁ : set R) (S₂ : set R): R → Prop 
  | empty_sum : linear_combination 0 
  | add_term (x : R) : ∀ s₁ s₂ l : R, s₁ ∈ S₁ → s₂ ∈ S₂ → linear_combination l → x = s₁ * s₂ + l → linear_combination x

structure ring_hom (R₁: Type u) (R₂ : Type v) [comm_ring R₁] [comm_ring R₂] : Type max u v :=
  (map : R₁ → R₂)
  (prevs_one : map 1 = 1)
  (prevs_mul : ∀ a b : R₁, map (a * b) = map a * map b)
  (prevs_add : ∀ a b : R₁, map (a + b) = map a + map b)

infixr `→ᵣ`:25 := ring_hom

instance ring_hom_to_function {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] : has_coe_to_fun (R₁ →ᵣ R₂) (λ _, R₁ → R₂) := ⟨λ φ, φ.map⟩ 

def idᵣ {R : Type u} [comm_ring R] : R →ᵣ R := 
  {
    map := id,
    prevs_one := rfl,
    prevs_mul := λ _ _, rfl,
    prevs_add := λ _ _, rfl,
  }

lemma compose_prevs_mul {R₁ : Type u} {R₂ : Type v} {R₃ : Type w}[comm_ring R₁] [comm_ring R₂] [comm_ring R₃] (φ₁ : R₂ →ᵣ R₃) (φ₂ : R₁ →ᵣ R₂)
  : ∀ a b : R₁, (⇑φ₁ ∘ ⇑φ₂) (a * b) = (⇑φ₁ ∘ ⇑φ₂) a * (⇑φ₁ ∘ ⇑φ₂) b :=
begin
  intros a b,
  exact calc (⇑φ₁ ∘ ⇑φ₂) (a * b) = φ₁.map (φ₂.map (a * b))               : rfl
                             ... = φ₁.map (φ₂.map a) * φ₁.map (φ₂.map b) : by simp [φ₂.prevs_mul ,φ₁.prevs_mul]
                             ... = (⇑φ₁ ∘ ⇑φ₂) a * (⇑φ₁ ∘ ⇑φ₂) b         : rfl
end 

lemma compose_prevs_add {R₁ : Type u} {R₂ : Type v} {R₃ : Type w}[comm_ring R₁] [comm_ring R₂] [comm_ring R₃] (φ₁ : R₂ →ᵣ R₃) (φ₂ : R₁ →ᵣ R₂)
  : ∀ a b : R₁, (⇑φ₁ ∘ ⇑φ₂) (a + b) = (⇑φ₁ ∘ ⇑φ₂) a + (⇑φ₁ ∘ ⇑φ₂) b :=
begin
  intros a b,
  exact calc (⇑φ₁ ∘ ⇑φ₂) (a + b) = φ₁.map (φ₂.map (a + b))               : rfl
                             ... = φ₁.map (φ₂.map a) + φ₁.map (φ₂.map b) : by simp [φ₂.prevs_add ,φ₁.prevs_add]
                             ... = (⇑φ₁ ∘ ⇑φ₂) a + (⇑φ₁ ∘ ⇑φ₂) b         : rfl
end

lemma compose_prevs_one {R₁ : Type u} {R₂ : Type v} {R₃ : Type w}[comm_ring R₁] [comm_ring R₂] [comm_ring R₃] (φ₁ : R₂ →ᵣ R₃) (φ₂ : R₁ →ᵣ R₂)
  : (⇑φ₁ ∘ ⇑φ₂) (1) = 1 :=
begin
  exact calc (⇑φ₁ ∘ ⇑φ₂) (1) = φ₁.map (φ₂.map (1)) : rfl
                         ... = 1                   : by simp [φ₂.prevs_one ,φ₁.prevs_one]
end

def ring_hom_comp {R₁ : Type u} {R₂ : Type v} {R₃ : Type w}[comm_ring R₁] [comm_ring R₂] [comm_ring R₃] (φ₁ : R₂ →ᵣ R₃) (φ₂ : R₁ →ᵣ R₂)
  : R₁ →ᵣ R₃ :=
  {
    map := ⇑φ₁ ∘ ⇑φ₂,
    prevs_one := compose_prevs_one φ₁ φ₂,
    prevs_add := compose_prevs_add φ₁ φ₂,
    prevs_mul := compose_prevs_mul φ₁ φ₂,
  }

infixr `∘ᵣ` : 25 := ring_hom_comp

theorem ring_hom_preserves_zero {R₁ : Type u} {R₂ : Type v} [l₁ :comm_ring R₁] [l₂:comm_ring R₂] (φ : R₁ →ᵣ R₂) : φ 0 = 0 :=
begin
  have sub : φ 0 = φ 0 + φ 0,
    exact calc φ 0 = φ (0 + 0) : by rw add_zero
               ... = φ 0 + φ 0 : φ.prevs_add 0 0,
  symmetry,
  exact calc 0 = φ 0 + - φ 0        : by rw ← minus_inverse
           ... = (φ 0 + φ 0) + -φ 0 : by rw ← sub
           ... = φ 0                : by rw [← add_assoc, minus_inverse, add_zero],
end

lemma minus_commutes_with_hom {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) : ∀ x : R₁, φ (-x) = - φ x :=
begin
  intro x,
  apply minus_unquie,
  have trv : φ.map = ⇑φ := rfl,
  rw [←trv, ← φ.prevs_add, minus_inverse,trv,ring_hom_preserves_zero],
end

theorem ring_hom_equality_hack {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] {φ₁ φ₂: R₁ →ᵣ R₂} 
: (⇑φ₁) = (φ₂.map) → φ₁ = φ₂ :=
begin
  intro h,
  cases φ₁,
  cases φ₂,
  rw ring_hom.mk.inj_eq,
  exact h,
end

theorem ring_hom_equality {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] {φ₁ φ₂: R₁ →ᵣ R₂} 
: (φ₁.map) = (φ₂.map) → φ₁ = φ₂ :=
begin
  intro h,
  cases φ₁,
  cases φ₂,
  rw ring_hom.mk.inj_eq,
  exact h,
end

def ring_isomorphism {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) : Prop := ∃ ψ : R₂ →ᵣ R₁, (ψ ∘ᵣ φ) = idᵣ ∧ (φ ∘ᵣ ψ) = idᵣ 

theorem id_hom_left_comp {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : (idᵣ ∘ᵣ φ) = φ :=
begin
  apply ring_hom_equality,
  refl,
end

theorem id_hom_right_comp {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : (φ ∘ᵣ idᵣ) = φ :=
begin
  apply ring_hom_equality,
  refl,
end

end comm_ring