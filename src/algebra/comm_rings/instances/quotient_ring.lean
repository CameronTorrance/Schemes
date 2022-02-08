import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances


namespace comm_ring

universes u v w

open set
open classical

def in_same_coset {R : Type u} [comm_ring R] (I: ideal R) : R → R → Prop := λ x y, x + -y ∈ I.body

notation x ` ≡ ` y ` mod ` I := in_same_coset I x y

lemma in_same_coset_refl {R : Type u} [comm_ring R] (I: ideal R) : ∀ x, x ≡ x mod I :=
begin
  intros x,
  have h : x + -x ∈ ↑I,
    rw minus_inverse,
    exact I.contains_zero,
  exact h,
end 

lemma in_same_coset_symm {R : Type u} [comm_ring R] (I: ideal R) : symmetric (in_same_coset I) :=
begin
  intros x y hxy,
  have h : y + -x ∈ ↑I,
    rw ← minus_minus y,
    rw ← minus_dis,
    apply I.minus_closure,
    rw add_comm,
    exact hxy,
  exact h,
end

lemma in_same_coset_trans {R : Type u} [comm_ring R] (I: ideal R) : transitive (in_same_coset I) :=
begin
  intros x y z hxy hyz,
  have hrw : x + -z = (x + -y) + (y + -z),
    exact calc x + -z = (x + 0) + -z   : by rw add_zero x
                  ... =  (x + -y) + (y +- z) : by {rw [←minus_inverse, add_comm y (-y)], simp [add_assoc]},
  have h : x + -z ∈ ↑I,
    rw hrw,
    apply I.add_closure,
    exact hxy,
    exact hyz,
  exact h,
end

lemma mod_respects_add {R : Type u} [comm_ring R] {I: ideal R} 
  : ∀ {x₁ x₂ y₁ y₂ : R} , (x₁ ≡ y₁ mod I) → (x₂ ≡ y₂ mod I) → ((x₁ + x₂) ≡ (y₁ + y₂) mod I) :=
begin
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  have hrw : (x₁ + x₂) + -(y₁ + y₂) = (x₁ + -y₁) + (x₂ + -y₂),
    exact calc (x₁ + x₂) + -(y₁ + y₂) = (x₁ + x₂) + (-y₁ + -y₂) : by rw minus_dis
                                  ... =  x₁ + (x₂ + -y₁) + -y₂  : by simp [add_assoc]
                                  ... =  x₁ + (-y₁ + x₂) + -y₂  : by simp [add_comm]
                                  ... = (x₁ + -y₁) + (x₂ + -y₂) : by simp [add_assoc],
  have h : (x₁ + x₂) + -(y₁ + y₂) ∈ ↑I,
    rw hrw,
    apply I.add_closure,
    exact h₁,
    exact h₂,
  exact h,
end

lemma mod_respects_mul {R : Type u} [comm_ring R] {I: ideal R} 
  : ∀ {x₁ x₂ y₁ y₂ : R} , (x₁ ≡ y₁ mod I) → (x₂ ≡ y₂ mod I) → ((x₁ * x₂) ≡ (y₁ * y₂) mod I) :=
begin
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  have hrw : x₁ * x₂ + -(y₁ * y₂) = x₁ * (x₂ + -y₂) + (x₁ + -y₁) * y₂,
    symmetry,
    exact calc x₁ * (x₂ + -y₂) + (x₁ + -y₁) * y₂ = (x₁ * x₂ + x₁ * (-y₂)) + y₂ * (x₁ + -y₁)       : by simp [mul_dis,mul_comm]
                                             ... = (x₁ * x₂ + x₁ * (-y₂)) + (x₁ * y₂ + (-y₁) *y₂) : by simp [mul_dis,mul_comm]
                                             ... = x₁ * x₂ + (x₁ * (-y₂) + x₁ * y₂) + (-y₁) * y₂  : by simp [add_assoc]
                                             ... = x₁ * x₂ + (x₁ * (-y₂ + y₂)) + ((-y₁) *y₂)      : by simp [←mul_dis]
                                             ... = x₁ * x₂ + (-y₁) * y₂                           : by simp [add_comm,minus_inverse,add_zero,mul_zero]
                                             ... = x₁ * x₂ + - (y₁ * y₂)                          : by rw [←minus_mul],
  have h : x₁ * x₂ + -(y₁ * y₂) ∈ ↑I,
    rw hrw,
    apply I.add_closure,
    apply I.mul_absorb,
    exact h₂,
    rw mul_comm,
    apply I.mul_absorb,
    exact h₁,
  exact h,
end

lemma mod_respects_minus {R : Type u} [comm_ring R] {I: ideal R}
  : ∀ {x y : R}, (x ≡ y mod I) → (-x ≡ -y mod I) :=
begin
  intros x y hxy,
  have h : -x + (-(-y)) ∈ ↑I,
    rw ← minus_dis,
    apply I.minus_closure,
    exact hxy,
  exact h,
end

def quotient_ring_setiod (R : Type u) [l:comm_ring R] (I: ideal R) : setoid R := 
  {
    r := λ x y, x ≡ y mod I,
    iseqv := ⟨in_same_coset_refl I, in_same_coset_symm I, in_same_coset_trans I⟩,
  }

def quotient_ring (R :Type u) [comm_ring R] (I : ideal R) : Type u := quotient (comm_ring.quotient_ring_setiod R I)

infixr  `/ᵣ` : 25 := quotient_ring  

def quotient_ring_mk {R : Type u} [comm_ring R] (I: ideal R) : R → R /ᵣ I := @quotient.mk R (quotient_ring_setiod R I)

infixr ` +ᵣ ` : 50 := λ x I , quotient_ring_mk I x

theorem quotient_ring_exists_rep {R: Type u} [comm_ring R] (I : ideal R) : ∀ q : R/ᵣ I, ∃ a : R, (a +ᵣ I) = q := @quotient.exists_rep R (quotient_ring_setiod R I)
theorem quotient_ring_sound {R: Type u} [comm_ring R] (I : ideal R) : ∀ {a b : R}, (a ≡ b mod I) → (a +ᵣ I) = (b +ᵣ I) := @quotient.sound R (quotient_ring_setiod R I)
theorem quotient_ring_exact {R: Type u} [comm_ring R] (I : ideal R) : ∀ {a b : R}, (a +ᵣ I) = (b +ᵣ I) → (a ≡ b mod I) := @quotient.exact R (quotient_ring_setiod R I)

def quotient_ring_one {R: Type u} [l:comm_ring R] (I:ideal R) : R /ᵣ I := l.one +ᵣ I

instance quotient_ring_has_one {R: Type u} [comm_ring R] (I:ideal R) : has_one (R /ᵣ I) := ⟨quotient_ring_one I⟩ 

theorem quotient_ring_concrete_char_of_one {R: Type u} [l:comm_ring R] (I:ideal R) : (l.one +ᵣ I) = 1 := rfl

def quotient_ring_zero {R: Type u} [l:comm_ring R] (I:ideal R) : R /ᵣ I := l.zero +ᵣ I

instance quotient_ring_has_zero {R: Type u} [comm_ring R] (I:ideal R) : has_zero (R /ᵣ I) := ⟨quotient_ring_zero I⟩ 

theorem quotient_ring_concrete_char_of_zero {R: Type u} [l:comm_ring R] (I:ideal R) : (l.zero +ᵣ I) = 0 := rfl

def quotient_ring_pre_add {R: Type u} [comm_ring R] (I:ideal R) : R → R → R /ᵣ I :=
  λ a b, (a + b) +ᵣ I

lemma quotient_ring_pre_add_lifts {R: Type u} [comm_ring R] (I:ideal R) 
  : ∀ x₁ x₂ y₁ y₂, (x₁ ≡ y₁ mod I) → (x₂ ≡ y₂ mod I) →  quotient_ring_pre_add I x₁ x₂ = quotient_ring_pre_add I y₁ y₂ := 
begin
  intros x₁ x₂ y₁ y₂,
  intros h₁ h₂,
  apply quotient.sound,
  apply mod_respects_add,
  exact h₁,
  exact h₂,
end

def quotient_ring_add {R: Type u} [comm_ring R] (I : ideal R) : (R /ᵣ I) → (R /ᵣ I) → R /ᵣ I :=
begin
  apply quotient.lift₂,
  exact quotient_ring_pre_add_lifts I,
end

instance quotient_ring_has_add {R: Type u} [comm_ring R] (I : ideal R) : has_add (R/ᵣI) := ⟨quotient_ring_add I⟩

theorem quotient_ring_concrete_char_of_add {R: Type u} [comm_ring R] (I : ideal R) : ∀ a b : R, (a +ᵣ I) + (b +ᵣ I) = ((a + b) +ᵣ I) :=
begin
  intros a b,
  refl,
end 

def quotient_ring_pre_mul {R: Type u} [comm_ring R] (I:ideal R) : R → R → R /ᵣ I :=
  λ a b, (a * b) +ᵣ I

lemma quotient_ring_pre_mul_lifts {R: Type u} [comm_ring R] (I:ideal R) 
  : ∀ x₁ x₂ y₁ y₂, (x₁ ≡ y₁ mod I) → (x₂ ≡ y₂ mod I) →  quotient_ring_pre_mul I x₁ x₂ = quotient_ring_pre_mul I y₁ y₂ := 
begin
  intros x₁ x₂ y₁ y₂,
  intros h₁ h₂,
  apply quotient.sound,
  apply mod_respects_mul,
  exact h₁,
  exact h₂,
end

def quotient_ring.mul {R: Type u} [comm_ring R] (I : ideal R) : (R /ᵣ I) → (R /ᵣ I) → R /ᵣ I :=
begin
  apply quotient.lift₂,
  exact quotient_ring_pre_mul_lifts I,
end

instance quotient_ring_has_mul {R: Type u} [comm_ring R] (I : ideal R) : has_mul (R/ᵣI) := ⟨quotient_ring.mul I⟩

theorem quotient_ring_concrete_char_of_mul {R: Type u} [comm_ring R] (I : ideal R) : ∀ a b : R, (a +ᵣ I) * (b +ᵣ I) = ((a * b) +ᵣ I) :=
begin
  intros a b,
  refl,
end

def quotient_ring_pre_minus {R: Type u} [comm_ring R] (I : ideal R) : R → (R/ᵣI) :=
  λ x : R, (-x) +ᵣ I

lemma quotient_ring_pre_minus_lifts {R: Type u} [comm_ring R] (I : ideal R) : ∀ x y, (x ≡ y mod I) → quotient_ring_pre_minus I x = quotient_ring_pre_minus I y :=
begin
  intros x y hxy,
  apply quotient.sound,
  apply mod_respects_minus,
  exact hxy,
end

def quotient_ring_minus {R: Type u} [comm_ring R] (I : ideal R) : (R /ᵣ I) → (R /ᵣ I) :=
begin
  apply quotient.lift,
  exact quotient_ring_pre_minus_lifts I,
end 

instance quotient_ring_has_neg {R: Type u} [comm_ring R] (I : ideal R) : has_neg (R/ᵣI) := ⟨quotient_ring_minus I⟩  

theorem quotient_ring_concrete_char_of_minus {R: Type u} [comm_ring R] (I : ideal R) : ∀ a : R, -(a +ᵣ I)  = (-a +ᵣ I) :=
begin
  intros a,
  refl,
end

theorem quotient_ring_add_assoc {R: Type u} [comm_ring R] (I : ideal R) : ∀ q₁ q₂ q₃ : (R /ᵣ I), q₁ + (q₂ + q₃) = (q₁ + q₂) +q₃ :=
begin
  intros q₁ q₂ q₃,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  let r₃ := some (quotient_ring_exists_rep I q₃),
  have hr₃ : (r₃ +ᵣ I) = q₃ := some_spec (quotient_ring_exists_rep I q₃),
  rw [←hr₁,←hr₂,←hr₃],
  simp [quotient_ring_concrete_char_of_add],
  rw add_assoc,
end

theorem quotient_ring_add_comm {R: Type u} [comm_ring R] (I : ideal R) : ∀ q₁ q₂ : (R /ᵣ I), q₁ + q₂ = q₂ + q₁ :=
begin
  intros q₁ q₂,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  rw [←hr₁,←hr₂],
  simp [quotient_ring_concrete_char_of_add],
  rw add_comm,
end

theorem quotient_ring_mul_assoc {R: Type u} [comm_ring R] (I : ideal R) : ∀ q₁ q₂ q₃ : (R /ᵣ I), q₁ * (q₂ * q₃) = (q₁ * q₂) * q₃ :=
begin
  intros q₁ q₂ q₃,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  let r₃ := some (quotient_ring_exists_rep I q₃),
  have hr₃ : (r₃ +ᵣ I) = q₃ := some_spec (quotient_ring_exists_rep I q₃),
  rw [←hr₁,←hr₂,←hr₃],
  simp [quotient_ring_concrete_char_of_mul],
  rw mul_assoc,
end

theorem quotient_ring_mul_comm {R: Type u} [comm_ring R] (I : ideal R) : ∀ q₁ q₂ : (R /ᵣ I), q₁ * q₂ = q₂ * q₁ :=
begin
  intros q₁ q₂,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  rw [←hr₁,←hr₂],
  simp [quotient_ring_concrete_char_of_mul],
  rw mul_comm,
end

theorem quotient_ring_mul_dis {R: Type u} [comm_ring R] (I : ideal R) : ∀ q₁ q₂ q₃ : (R /ᵣ I), q₁ * (q₂ + q₃) = (q₁ * q₂) + (q₁ * q₃) :=
begin
  intros q₁ q₂ q₃,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  let r₃ := some (quotient_ring_exists_rep I q₃),
  have hr₃ : (r₃ +ᵣ I) = q₃ := some_spec (quotient_ring_exists_rep I q₃),
  rw [←hr₁,←hr₂,←hr₃],
  simp [quotient_ring_concrete_char_of_mul,quotient_ring_concrete_char_of_add],
  rw mul_dis,
end

theorem quotient_ring_mul_one {R: Type u} [comm_ring R] (I : ideal R) : ∀ q : (R /ᵣ I), q * 1 = q :=
begin
  intro q,
  let r := some (quotient_ring_exists_rep I q),
  have hr : (r +ᵣ I) = q := some_spec (quotient_ring_exists_rep I q),
  rw [←hr,←quotient_ring_concrete_char_of_one],
  simp [quotient_ring_concrete_char_of_mul],
  rw mul_one,
end

theorem quotient_ring_add_zero {R: Type u} [comm_ring R] (I : ideal R) : ∀ q : (R /ᵣ I), q + 0 = q :=
begin
  intro q,
  let r := some (quotient_ring_exists_rep I q),
  have hr : (r +ᵣ I) = q := some_spec (quotient_ring_exists_rep I q),
  rw [←hr,←quotient_ring_concrete_char_of_zero],
  simp [quotient_ring_concrete_char_of_add],
  rw add_zero,
end

theorem quotient_ring_minus_inverse {R: Type u} [comm_ring R] (I : ideal R) : ∀ q : (R /ᵣ I), q + -q = 0 :=
begin
  intro q,
  let r := some (quotient_ring_exists_rep I q),
  have hr : (r +ᵣ I) = q := some_spec (quotient_ring_exists_rep I q),
  rw [←hr,←quotient_ring_concrete_char_of_zero],
  simp [quotient_ring_concrete_char_of_add, quotient_ring_concrete_char_of_minus],
  rw minus_inverse,
end

instance quotient_ring_comm_ring {R: Type u} [comm_ring R] (I : ideal R) : comm_ring (R/ᵣI) :=
begin
  split,
  exact quotient_ring_add_assoc I,
  exact quotient_ring_add_comm I,
  exact quotient_ring_add_zero I,
  exact quotient_ring_minus_inverse I,
  exact quotient_ring_mul_assoc I,
  exact quotient_ring_mul_comm I,
  exact quotient_ring_mul_one I,
  exact quotient_ring_mul_dis I,
end

def quot_ring_hom {R: Type u} [comm_ring R] (I : ideal R) : R →ᵣ (R/ᵣI) :=
  {
    map := λ x, x +ᵣ I,
    prevs_mul := λ _ _, rfl,
    prevs_add := λ _ _, rfl,
    prevs_one := rfl, 
  }

theorem quotient_zero_implies_in_ideal {R: Type u} [comm_ring R] (I : ideal R) 
  : ∀ {x : R} , (x +ᵣ I) = 0 → x ∈ I.body := 
begin
  intros x hx,
  rw [←add_zero x,← minus_zero_zero],
  have hrw : (x ≡ 0 mod I) = ((x +-0) ∈ I.body) := rfl,
  rw ← hrw,
  apply quotient_ring_exact,
  exact hx,
end

theorem in_ideal_implies_quotient_zero {R: Type u} [comm_ring R] (I : ideal R) 
  : ∀ {x : R} , x ∈ I.body → (x +ᵣ I) = 0 :=
begin
  intros x hx,
  rw ← quotient_ring_concrete_char_of_zero,
  apply quotient_ring_sound,
  rw [←add_zero x,← minus_zero_zero] at hx,
  exact hx,
end

theorem quot_ring_hom_kernel {R: Type u} [l:comm_ring R] (I : ideal R) : ker (quot_ring_hom I) = I :=
begin
  apply ideal_equality,
  apply subset_antisymmetric,
  split,
  intros x hx,
  apply quotient_zero_implies_in_ideal,
  apply zero_ideal_is_just_zero,
  exact hx,
  intros x hx,
  have h₁: (x +ᵣ I) = 0,
    apply in_ideal_implies_quotient_zero,
    exact hx,
  have h: (x +ᵣ I) ∈ (zero_ideal (R/ᵣI)).body,
    rw h₁,
    exact linear_combination.empty_sum,
  exact h,
end

def quot_ring_universal_property {R: Type u} [lR:comm_ring R] (I : ideal R) 
  : (Σ (Q : Type v) [lQ:comm_ring Q], (@ring_hom R Q lR lQ)) → Prop 
  | ⟨Q,lQ,φ⟩ := (∀ r : R, r ∈ I.body → φ r = lQ.zero) ∧ 
    (∀ pair : (Σ (Q : Type w) [lQ:comm_ring Q], (@ring_hom R Q lR lQ)),
    (∀ r : R, r ∈ I.body → pair.2.2 r = pair.2.1.zero) 
     → ∃! ψ : (@ring_hom Q pair.1 lQ pair.2.1) , pair.2.2 = (@ring_hom_comp R Q pair.1 lR lQ pair.2.1 ψ φ))

def quot_ring_app_lifts {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : ∀ r₁ r₂ : R, (r₁ ≡ r₂ mod I) →  φ r₁ =  φ r₂ :=
begin
  intros r₁ r₂ h₁₂,
  have hrw : r₁ = r₂ + (r₁ + -r₂),
    rw [add_comm r₁ (-r₂),add_assoc,minus_inverse],
    rw [add_comm,add_zero],
  rw hrw,
  have trv : φ.map = ⇑φ := rfl,
  rw [←trv,φ.prevs_add,trv, hφvan (r₁ + -r₂) h₁₂,add_zero],
end

def quot_ring_can_map {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : (R/ᵣI) → Q :=
begin
  apply quotient.lift,
  exact quot_ring_app_lifts I lQ φ hφvan,
end

theorem quotient_ring_concrete_char_of_can_map {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : ∀ x : R, quot_ring_can_map I lQ φ hφvan (x +ᵣ I) = φ x :=
begin
  intro,
  refl,
end

theorem quot_ring_can_map_prevs_add {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : ∀ q₁ q₂ : (R/ᵣI), quot_ring_can_map I lQ φ hφvan (q₁ + q₂) = (quot_ring_can_map I lQ φ hφvan q₁) + (quot_ring_can_map I lQ φ hφvan q₂) :=
begin
  intros q₁ q₂,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  rw [←hr₁,←hr₂],
  simp [quotient_ring_concrete_char_of_add I, quotient_ring_concrete_char_of_can_map],
  exact φ.prevs_add r₁ r₂,
end

theorem quot_ring_can_map_prevs_mul {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : ∀ q₁ q₂ : (R/ᵣI), quot_ring_can_map I lQ φ hφvan (q₁ * q₂) = (quot_ring_can_map I lQ φ hφvan q₁) * (quot_ring_can_map I lQ φ hφvan q₂) :=
begin
  intros q₁ q₂,
  let r₁ := some (quotient_ring_exists_rep I q₁),
  have hr₁ : (r₁ +ᵣ I) = q₁ := some_spec (quotient_ring_exists_rep I q₁),
  let r₂ := some (quotient_ring_exists_rep I q₂),
  have hr₂ : (r₂ +ᵣ I) = q₂ := some_spec (quotient_ring_exists_rep I q₂),
  rw [←hr₁,←hr₂],
  simp [quotient_ring_concrete_char_of_mul I, quotient_ring_concrete_char_of_can_map],
  exact φ.prevs_mul r₁ r₂,
end

theorem quot_ring_can_map_prevs_one {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : quot_ring_can_map I lQ φ hφvan 1 = 1 :=
begin
  simp [←quotient_ring_concrete_char_of_one,quotient_ring_concrete_char_of_can_map],
  exact φ.prevs_one,
end
  
def quot_ring_can_hom {R : Type u} {Q : Type v} [comm_ring R] (I : ideal R) (lQ:comm_ring Q) (φ : R →ᵣ Q) (hφvan : ∀ r : R , r ∈ I.body → φ r = 0)
  : ((R/ᵣI) →ᵣ Q) := 
  {
    map := quot_ring_can_map I lQ φ hφvan,
    prevs_add := quot_ring_can_map_prevs_add I lQ φ hφvan,
    prevs_mul := quot_ring_can_map_prevs_mul I lQ φ hφvan,
    prevs_one := quot_ring_can_map_prevs_one I lQ φ hφvan,
  }

theorem quotient_ring_satisfies_its_universal_property {R : Type u} [comm_ring R] (I :ideal R) 
  : quot_ring_universal_property I ⟨(R/ᵣI),comm_ring.quotient_ring_comm_ring I,quot_ring_hom I⟩ :=
begin
  split,
  intros x hx,
  rw ← quot_ring_hom_kernel I at hx,
  apply zero_ideal_is_just_zero,
  exact hx,
  intros pair hpair,
  cases pair with Q rest,
  cases rest with lQ φ,
  existsi (quot_ring_can_hom I lQ φ hpair),
  split,
  apply ring_hom_equality,
  refl,
  intros φ' hφ',
  apply ring_hom_equality_hack,
  have trv₁ : ∀ x : R , φ x = φ' (x +ᵣ I),
    simp at hφ',
    intros x,
    rw hφ',
    refl, 
  apply funext,
  intro q,
  let r := some (quotient_ring_exists_rep I q),
  have hr : (r +ᵣ I) = q := some_spec (quotient_ring_exists_rep I q),
  rw ← hr,
  simp,
  rw ← trv₁ r,
  refl,
end

theorem universal_property_chars_quotient_ring {R : Type u} [lR:comm_ring R] {Q :Type v} [lQ : comm_ring Q] 
  {Q' : Type w} [lQ' : comm_ring Q'] {I : ideal R} (φ : R →ᵣ Q) (φ' : R →ᵣ Q') 
    : quot_ring_universal_property I ⟨Q,lQ,φ⟩ → quot_ring_universal_property I ⟨Q',lQ',φ'⟩
    → ∃! ψ : Q →ᵣ Q', φ' = (ψ ∘ᵣ φ) ∧ (ring_isomorphism ψ) := 
begin
  intros upQ upQ',
  sorry,
end

end comm_ring