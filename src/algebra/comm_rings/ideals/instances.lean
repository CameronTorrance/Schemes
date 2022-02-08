import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic

namespace comm_ring

universes u v

open set
open classical

def univ_as_ideal {R : Type u} [comm_ring R] : ideal R :=
{
  body := univ,
  contains_zero := trivial,
  minus_closure := λ _ _, trivial,
  add_closure := λ _ _ _ _, trivial,
  mul_absorb := λ _ _ _, trivial,
}

def ideal_generated_by_set_set {R : Type u} [comm_ring R] (S : set R) : set R := λ x, linear_combination univ S x

lemma ideal_gen_set_contains_zero {R : Type u} [l:comm_ring R] (S : set R) : l.zero ∈ ideal_generated_by_set_set S :=
begin
  exact linear_combination.empty_sum,
end

lemma ideal_gen_set_add_closure {R : Type u} [comm_ring R] (S : set R) :
   ∀ (a b : R), (a ∈ ideal_generated_by_set_set S) → (b ∈ ideal_generated_by_set_set S) 
   → (a + b ∈ ideal_generated_by_set_set S) :=
begin
  intros a b ha hb,
  induction ha with x r s l hx hs hl sum hlb,
  rw add_comm,
  rw add_zero,
  exact hb,
  rw sum,
  rw ← add_assoc,
  apply linear_combination.add_term,
  exact hx,
  exact hs,
  exact hlb,
  refl,
end

lemma ideal_gen_set_minus_closure {R : Type u} [comm_ring R] (S : set R) 
  : ∀ r : R, r ∈ ideal_generated_by_set_set S → -r ∈ ideal_generated_by_set_set S :=
begin
  intros r hr,
  induction hr with r a b l hainuniv hbinS hl hr hminusl,
  rw minus_zero_zero,
  exact ideal_gen_set_contains_zero S,
  rw [hr,minus_dis,minus_mul],
  apply linear_combination.add_term,
  trivial,
  exact hbinS,
  exact hminusl,
  refl,
end

lemma ideal_gen_set_mul_absorb {R : Type u} [comm_ring R] (S : set R) 
  : ∀ r : R, ∀ {i : R}, i ∈ ideal_generated_by_set_set S → (r * i) ∈ ideal_generated_by_set_set S :=
begin
  intros r i hi,
  induction hi with  i y s l hy hs hl sum hlb,
  rw mul_zero,
  exact linear_combination.empty_sum,
  rw sum,
  rw [mul_dis,mul_assoc],
  apply linear_combination.add_term,
  trivial,
  exact hs,
  exact hlb,
  refl,
end

def ideal_generated_by_set {R : Type u} [comm_ring R] (S : set R) : ideal R :=
{
  body := ideal_generated_by_set_set S,
  contains_zero := ideal_gen_set_contains_zero S,
  minus_closure := ideal_gen_set_minus_closure S,
  mul_absorb := ideal_gen_set_mul_absorb S,
  add_closure := ideal_gen_set_add_closure S,
}

def zero_ideal (R : Type u) [comm_ring R] : ideal R := ideal_generated_by_set (λ x, x = 0)

theorem zero_ideal_is_just_zero {R : Type u} [comm_ring R] : ∀ {x : R} , x ∈ (zero_ideal R).body → x = 0 :=
begin
  intros x hx,
  induction hx with y s₁ s₂ l hs₁ hs₂ hl sum hsum,
  refl,
  rw sum,
  have zs₂ : s₂ = 0 := hs₂,
  rw [zs₂,mul_zero,hsum,add_zero],
end

theorem zero_ideal_proper {R : Type u} [comm_ring R] (not_zero : ∃ x : R , x ≠ 0) : ↑(zero_ideal R) ≠ @univ R :=
begin
  intro ab,
  let x := some not_zero,
  have hx : x ≠ 0 := some_spec not_zero,
  apply hx,
  have hxuniv : x ∈ @univ R := trivial,
  rw ← ab at hxuniv,
  apply zero_ideal_is_just_zero,
  exact hxuniv,  
end

def product_of_ideals_set {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : set R :=
  λ x, linear_combination ↑I₁ ↑I₂ x

lemma product_of_ideals_contains_zero {R : Type u} [l:comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : l.zero ∈ product_of_ideals_set I₁ I₂ :=
  linear_combination.empty_sum

lemma product_of_ideals_add_closure {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ i₁ i₂ : R, i₁ ∈ product_of_ideals_set I₁ I₂ → i₂ ∈ product_of_ideals_set I₁ I₂
    → i₁ + i₂ ∈ product_of_ideals_set I₁ I₂ :=
begin
  intros i₁ i₂ hi₁ hi₂,
  induction hi₂ with i₂ s₁ s₂ l hs₁ hs₂ hl hi₂  hsum,
  rw add_zero,
  exact hi₁,
  rw hi₂,
  have sub : i₁ + (s₁ * s₂ + l) = s₁ * s₂ + (i₁ + l),
    simp [add_assoc,add_comm],
  rw sub,
  apply linear_combination.add_term,
  exact hs₁,
  exact hs₂,
  exact hsum,
  refl,
end

lemma product_of_ideals_mul_absorb {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ r : R, ∀ {i : R}, i ∈ product_of_ideals_set I₁ I₂ → (r * i) ∈ product_of_ideals_set I₁ I₂ :=
begin
  intros r i hi,
  induction hi with i i₁ i₂ l hi₁ hi₂ hl hi hprod,
  rw mul_zero,
  exact linear_combination.empty_sum,
  rw hi,
  rw mul_dis,
  rw mul_assoc,
  apply linear_combination.add_term,
  apply I₁.mul_absorb,
  exact r,
  exact hi₁,
  exact hi₂,
  exact hprod,
  refl,
end

lemma product_of_ideals_minus_closure {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ a, a ∈ product_of_ideals_set I₁ I₂ → -a ∈ product_of_ideals_set I₁ I₂ :=
begin
  intros a ha,
  induction ha with a i₁ i₂ l hi₁ hi₂ hl ha hlminus,
  rw minus_zero_zero,
  exact product_of_ideals_contains_zero I₁ I₂,
  rw [ha, minus_dis,minus_mul],
  apply linear_combination.add_term,
  apply I₁.minus_closure,
  exact hi₁,
  exact hi₂,
  exact hlminus,
  refl,
end

def product_of_ideals {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : ideal R := 
  {
    body          := product_of_ideals_set I₁ I₂,
    contains_zero := product_of_ideals_contains_zero I₁ I₂,
    minus_closure := product_of_ideals_minus_closure I₁ I₂,
    add_closure   := product_of_ideals_add_closure I₁ I₂,
    mul_absorb    := product_of_ideals_mul_absorb I₁ I₂
  }

instance mul_ideals {R : Type u} [comm_ring R] : has_mul (ideal R) := ⟨ λ I₁ I₂, product_of_ideals I₁ I₂⟩ 

def sum_of_ideals_set {R : Type u} [l:comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : set R := λ r : R, ∃ i₁ i₂ : R, i₁ ∈ I₁.body ∧ i₂ ∈ I₂.body ∧ r = i₁ + i₂

lemma half_sum_of_pairs_set_commuative {R :Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : sum_of_ideals_set I₁ I₂ ⊆ sum_of_ideals_set I₂ I₁ :=
begin
  intros x hx,
  cases hx with x₁ hx₁,
  cases hx₁ with x₂ hx₁x₂,
  cases hx₁x₂ with hx₁inI₁ the_rest,
  cases the_rest with hx₂inI₂ hx,
  existsi x₂,
  existsi x₁,
  split,
  exact hx₂inI₂,
  split,
  exact hx₁inI₁,
  rw add_comm,
  exact hx,
end

lemma sum_of_pair_of_ideals_upper_bound {R :Type u} [l:comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ↑I₁ ⊆ sum_of_ideals_set I₁ I₂ :=
begin
  intros i hi,
  existsi i,
  existsi l.zero,
  split,
  exact hi,
  split,
  exact I₂.contains_zero,
  rw add_zero,
end

lemma sum_of_ideals_contains_zero {R : Type u} [l:comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : l.zero ∈ sum_of_ideals_set I₁ I₂ :=
begin
  existsi l.zero,
  existsi l.zero,
  split,
  exact I₁.contains_zero,
  split,
  exact I₂.contains_zero,
  rw add_zero l.zero,
end

lemma sum_of_ideals_add_closure {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ a b, a ∈ sum_of_ideals_set I₁ I₂ → b ∈ sum_of_ideals_set I₁ I₂ → a + b ∈ sum_of_ideals_set I₁ I₂ :=
begin
  intros a b ha hb,
  cases ha with a₁ ha₁,
  cases ha₁ with a₂ ha₁a₂,
  cases ha₁a₂ with ha₁inI₁ the_rest,
  cases the_rest with ha₂inI₂ ha,
  cases hb with b₁ hb₁,
  cases hb₁ with b₂ hb₁b₂,
  cases hb₁b₂ with hb₁inI₁ the_rest,
  cases the_rest with hb₂inI₂ hb,
  existsi a₁ + b₁,
  existsi a₂ + b₂,
  split,
  apply I₁.add_closure,
  exact ha₁inI₁,
  exact hb₁inI₁,
  split,
  apply I₂.add_closure,
  exact ha₂inI₂,
  exact hb₂inI₂,
  rw [ha,hb],
  exact calc (a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + b₁) + b₂   : by simp [add_assoc]
                               ... = (a₁ + b₁) + (a₂ + b₂) : by {rw add_comm a₂ b₁,simp [add_assoc]},
end 

lemma sum_of_ideals_mul_absorb {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ r : R, ∀ {i}, i ∈ sum_of_ideals_set I₁ I₂ → r * i ∈ sum_of_ideals_set I₁ I₂ :=
begin
  intros r i hi,
  cases hi with i₁ hi₁,
  cases hi₁ with i₂ hi₁i₂,
  cases hi₁i₂ with hi₁inI₁ the_rest,
  cases the_rest with hi₂inI₂ hi,
  rw hi,
  rw mul_dis,
  apply sum_of_ideals_add_closure,
  apply sum_of_pair_of_ideals_upper_bound,
  apply I₁.mul_absorb,
  exact hi₁inI₁,
  apply half_sum_of_pairs_set_commuative,
  apply sum_of_pair_of_ideals_upper_bound,
  apply I₂.mul_absorb,
  exact hi₂inI₂,
end

lemma sum_of_ideals_minus_closure {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) 
  : ∀ i : R, i ∈ sum_of_ideals_set I₁ I₂ → -i ∈ sum_of_ideals_set I₁ I₂ :=
begin
  intros i hi,
  cases hi with i₁ hi₁,
  cases hi₁ with i₂ hi₁i₂,
  cases hi₁i₂ with hi₁inI₁ the_rest,
  cases the_rest with hi₂inI₂ hi,
  existsi -i₁,
  existsi -i₂,
  split,
  apply I₁.minus_closure,
  exact hi₁inI₁,
  split,
  apply I₂.minus_closure,
  exact hi₂inI₂,
  rw [hi,minus_dis],
end

def sum_of_ideals {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : ideal R :=
  {
    body := sum_of_ideals_set I₁ I₂,
    contains_zero := sum_of_ideals_contains_zero I₁ I₂,
    minus_closure := sum_of_ideals_minus_closure I₁ I₂,
    add_closure := sum_of_ideals_add_closure I₁ I₂,
    mul_absorb := sum_of_ideals_mul_absorb I₁ I₂,
  }

instance add_ideals {R : Type u} [comm_ring R] (I₁ : ideal R) (I₂ : ideal R) : has_add (ideal R) := ⟨λ I₁ I₂, sum_of_ideals I₁ I₂⟩ 

def preimage_set {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂) : set R₁ :=
  λ r : R₁, φ r ∈ I.body 

theorem preimage_add_closure {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂) 
  : ∀ r₁ r₂ : R₁, r₁ ∈ (preimage_set φ I) → r₂ ∈ (preimage_set φ I) → (r₁ + r₂) ∈ (preimage_set φ I) :=
begin
  intros r₁ r₂ hr₁ hr₂,
  have h: φ.map (r₁ + r₂) ∈ ↑I,
    rw φ.prevs_add,
    apply I.add_closure,
    exact hr₁,
    exact hr₂,
  exact h,  
end

theorem preimage_mul_absorb {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂)
  : ∀ r : R₁, ∀ {i : R₁}, i ∈ preimage_set φ I → (r * i) ∈ preimage_set φ I :=
begin
  intros r i hi,
  have h : φ.map (r * i) ∈ ↑I,
    rw φ.prevs_mul,
    apply I.mul_absorb,
    exact hi,
  exact h,
end

theorem preimage_contains_zero {R₁ : Type u} [l:comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂) 
  : l.zero ∈ preimage_set φ I :=
begin
  have trv : φ.map = ⇑φ := rfl,
  have h : φ.map 0 ∈ ↑I,
    rw trv,
    rw ring_hom_preserves_zero φ,
    exact I.contains_zero,
  exact h,
end

theorem preimage_of_ideal_minus_closure {R₁ : Type u} [comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂)
  : ∀ x : R₁, x ∈ preimage_set φ I → -x ∈ preimage_set φ I :=
begin
  intros x hx,
  have h : φ (-x) ∈ ↑I,
    rw minus_commutes_with_hom,
    apply I.minus_closure,
    exact hx,
  exact h,
end

def preimage_of_ideal {R₁ : Type u} [l:comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) (I : ideal R₂) : ideal R₁ :=
  {
    body := preimage_set φ I,
    contains_zero := preimage_contains_zero φ I,
    minus_closure := preimage_of_ideal_minus_closure φ I,
    add_closure := preimage_add_closure φ I,
    mul_absorb := preimage_mul_absorb φ I,
  }

def ker {R₁ : Type u} [l:comm_ring R₁] {R₂ : Type v} [comm_ring R₂] (φ : R₁ →ᵣ R₂) : ideal R₁ := preimage_of_ideal φ (zero_ideal R₂) 

end comm_ring