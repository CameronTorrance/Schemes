import algebra.comm_rings.basic
import misc.set

namespace comm_ring

universe u

open set

structure ideal (R : Type u) [l:comm_ring R] :=
  (body : set R)
  (contains_zero : l.zero ∈ body)
  (minus_closure : ∀ a : R, a ∈ body → -a ∈ body)
  (add_closure : ∀ a b : R, a ∈ body → b ∈ body → (a + b) ∈ body)
  (mul_absorb : ∀ r : R, ∀ {i : R}, i ∈ body → (r * i) ∈ body)

instance ideal_to_set {R : Type u} [comm_ring R] : has_coe (ideal R) (set R) := ⟨λ I : ideal R, I.body⟩

structure proper_ideal (R : Type u) [l:comm_ring R] :=
  (body : set R)
  (contains_zero : l.zero ∈ body)
  (minus_closure : ∀ a : R, a ∈ body → -a ∈ body)
  (add_closure : ∀ a b : R, a ∈ body → b ∈ body → (a + b) ∈ body)
  (mul_absorb : ∀ r : R, ∀ {i : R}, i ∈ body → (r * i) ∈ body)
  (proper : body ≠ univ)

def proper_ideals_are_ideals {R : Type u} [l:comm_ring R] : proper_ideal R → ideal R :=
begin
  intro I,
  split,
  exact I.contains_zero,
  exact I.minus_closure,
  exact I.add_closure,
  exact I.mul_absorb,
end

instance proper_ideals_to_ideals {R : Type u} [comm_ring R] : has_coe (proper_ideal R) (ideal R) := ⟨proper_ideals_are_ideals⟩ 

structure Spec (R : Type u) [l:comm_ring R] :=
  (body : set R)
  (contains_zero : l.zero ∈ body)
  (minus_closure : ∀ a : R, a ∈ body → -a ∈ body)
  (add_closure : ∀ a b : R, a ∈ body → b ∈ body → (a + b) ∈ body)
  (mul_absorb : ∀ r : R, ∀ {i : R}, i ∈ body → (r * i) ∈ body)
  (prime : ∀ r₁ r₂ : R, r₁ * r₂ ∈ body → r₁ ∈ body ∨ r₂ ∈ body)
  (proper : body ≠ univ)

def prime_ideals_are_proper_ideals (R : Type u) [comm_ring R] : Spec R → proper_ideal R :=
begin
  intro I,
  split,
  exact I.contains_zero,
  exact I.minus_closure,
  exact I.add_closure,
  exact I.mul_absorb,
  exact I.proper,
end

instance prime_ideals_to_proper_ideals {R : Type u} [comm_ring R] : has_coe (Spec R) (proper_ideal R) := ⟨prime_ideals_are_proper_ideals R⟩ 

structure MaxSpec (R : Type u) [l:comm_ring R] :=
  (body : set R)
  (contains_zero : l.zero ∈ body)
  (minus_closure : ∀ a : R, a ∈ body → -a ∈ body)
  (add_closure : ∀ a b : R, a ∈ body → b ∈ body → (a + b) ∈ body)
  (mul_absorb : ∀ r  : R, ∀ {i}, i ∈ body → (r * i) ∈ body)
  (maximal: ∀ I : ideal R, body ⊆ I → ↑I = body ∨ ↑I = @univ R)
  (proper : body ≠ univ)

def is_prime {R: Type u} [comm_ring R] : proper_ideal R → Prop 
  := λ I: proper_ideal R, ∀ r₁ r₂ : R, (r₁ * r₂) ∈ I.body → r₁ ∈ I.body ∨ r₂ ∈ I.body

def is_maximal {R : Type u} [comm_ring R] : proper_ideal R → Prop 
  := λ I : proper_ideal R, ∀ J : ideal R, I.body ⊆ J → ↑J = I.body ∨ J.body = univ 

def ideal_to_proper {R : Type u} [comm_ring R] :  Π {I : ideal R} , ↑I ≠ @univ R → proper_ideal R :=
begin
  intros I hI,
  split,
  exact I.contains_zero,
  exact I.minus_closure,
  exact I.add_closure,
  exact I.mul_absorb,
  exact hI,
end 

def proper_to_prime {R : Type u} [comm_ring R] : Π {I : proper_ideal R} , is_prime I → Spec R :=
begin
  intros I hI,
  split,
  exact I.contains_zero,
  exact I.minus_closure,
  exact I.add_closure,
  exact I.mul_absorb,
  exact hI,
  exact I.proper,
end 

def proper_to_maximal {R : Type u} [comm_ring R] : Π {I : proper_ideal R} , is_maximal I → MaxSpec R :=
begin
  intros I hI,
  split,
  exact I.contains_zero,
  exact I.minus_closure,
  exact I.add_closure,
  exact I.mul_absorb,
  exact hI,
  exact I.proper,
end 

theorem proper_ideal_equality {R : Type u} [comm_ring R] : ∀ {I₁ I₂ : proper_ideal R}, I₁.body = I₂.body → I₁ = I₂ :=
begin
  intros I₁ I₂ h,
  cases I₁,
  cases I₂,
  rw proper_ideal.mk.inj_eq,
  exact h,
end

theorem ideal_equality {R : Type u} [comm_ring R] : ∀ {I₁ I₂ : ideal R}, I₁.body = I₂.body → I₁ = I₂ :=
begin
  intros I₁ I₂ h,
  cases I₁,
  cases I₂,
  rw ideal.mk.inj_eq,
  exact h,
end

lemma ideal_containing_unit_is_univ {R : Type u} [comm_ring R] (I : ideal R) : ∀ {x : R}, unit x → x ∈ I.body → ↑I = @univ R :=
begin
  intros x hxunit hxinI,
  apply subset_antisymmetric,
  split,
  intros _ _,
  trivial,
  intros y _,
  cases hxunit with a ha,
  have haxinI : a * x ∈ ↑I,
    apply I.mul_absorb,
    exact hxinI,
  rw ha at haxinI,
  have ha1inI : y * 1 ∈ ↑I,
    apply I.mul_absorb,
    exact haxinI,
  rw mul_one at ha1inI,
  exact ha1inI,
end

lemma unit_not_in_proper_ideal {R : Type u} [comm_ring R] : ∀ {x : R}, ∀ {I : proper_ideal R}, unit x → x ∉ I.body :=
begin
  intros x I hx h,
  apply I.proper,
  let J : ideal R := proper_ideals_are_ideals I,
  have trv : I.body = J.body := rfl,
  rw trv,
  apply ideal_containing_unit_is_univ J,
  exact hx,
  exact h,
end

end comm_ring