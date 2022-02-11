import algebra.comm_rings.basic

namespace comm_ring

universes u v

instance int_is_ring : comm_ring ℤ :=
begin
  split,
  intros a b c,
  symmetry,
  exact int.add_assoc a b c,
  exact int.add_comm,
  exact int.add_zero,
  exact int.add_right_neg,
  intros a b c,
  symmetry,
  exact int.mul_assoc a b c,
  exact int.mul_comm,
  exact int.mul_one,
  exact int.distrib_left,
end

def initial_ring : (Σ R : Type u, comm_ring R) → Prop
  | ⟨R,lR⟩ := ∀ pair : (Σ R' : Type u, comm_ring R'), ∃! ψ : @ring_hom R pair.1 lR pair.2, true


def int_hom_map (R : Type u) [comm_ring R] : ℤ → R
  | (int.of_nat n)          := nat_to_ring R n
  | (int.neg_succ_of_nat n) := -1 + - (nat_to_ring R n)


lemma int_hom_of_nat {R : Type u} [comm_ring R] : ∀ {n : ℕ}, int_hom_map R (int.of_nat n) = nat_to_ring R n := λ _, rfl

theorem int_hom_prevs_zero {R : Type u} [lR:comm_ring R] : int_hom_map R int.zero = lR.zero := rfl

inductive zero_ring : Type
  | elm : zero_ring


theorem zero_ring_has_one_element : ∀ x : zero_ring, x = zero_ring.elm :=
begin
  intro x,
  cases x,
  refl,
end

instance zero_ring_is_ring : comm_ring zero_ring :=
  {
    add := λ _ _, zero_ring.elm,
    mul := λ _ _, zero_ring.elm,
    zero := zero_ring.elm,
    one := zero_ring.elm,
    mul_dis := λ _ _ _, rfl,
    mul_assoc := λ _ _ _, rfl,
    mul_comm := λ _ _, rfl,
    mul_one := 
    begin
      intro a,
      cases a,
      refl,
    end,
    add_assoc := λ _ _ _, rfl,
    add_comm := λ _ _, rfl,
    add_zero :=
    begin
      intro a,
      cases a,
      refl,
    end,
    neg := λ _, zero_ring.elm,
    minus_inverse := λ _, rfl,
  }


def zero_ring_hom (R : Type u) [l:comm_ring R] : R →ᵣ zero_ring:=
  {
    map := λ _, zero_ring.elm,
    prevs_add := λ _ _, rfl,
    prevs_mul := λ _ _,rfl,
    prevs_one := rfl,
  }

def final_ring : (Σ R : Type u, comm_ring R) → Prop
  | ⟨R,lR⟩ := ∀ pair : (Σ R' : Type u, comm_ring R'), ∃! ψ : @ring_hom pair.1  R  pair.2 lR , true

def final_ring_hom_id {Z : Type u} [lZ: comm_ring Z] : final_ring ⟨Z,lZ⟩ → ∀ φ : Z →ᵣ Z, φ = idᵣ :=
begin
  intros upZ φ,
  cases upZ ⟨Z,lZ⟩ with φ_int hφ_int,
  cases hφ_int with trv hφ.raw,
  simp at hφ.raw,
  have h₁ := hφ.raw idᵣ trivial,
  have h₂ := hφ.raw φ trivial,
  rw [h₁,h₂],
end

theorem zero_ring_is_final : final_ring ⟨zero_ring,comm_ring.zero_ring_is_ring⟩ :=
begin
  intro pair,
  cases pair with R lR,
  existsi @zero_ring_hom R lR,
  split,
  trivial,
  intros φ trv,
  apply ring_hom_equality,
  apply funext,
  intro x,
  apply zero_ring_has_one_element,
end


theorem final_ring_unique {R₁ R₂: Type u} [lR₁ : comm_ring R₁] [lR₂ : comm_ring R₂]
  : final_ring ⟨R₁,lR₁⟩  → final_ring ⟨R₂,lR₂⟩
  → ∃! ψ : R₁ →ᵣ R₂ , ring_isomorphism ψ :=
begin
  intros R₁up R₂up ,
  cases R₁up ⟨R₂,lR₂⟩ with φ₁ hφ₁,
  cases R₂up ⟨R₁,lR₁⟩ with φ₂ hφ₂,
  existsi φ₂,
  split,
  existsi φ₁,
  split,
  apply final_ring_hom_id,
  exact R₁up,
  apply final_ring_hom_id,
  exact R₂up,
  simp,
  simp at hφ₂,
  intros ψ hψ,
  apply λ y, hφ₂ y trivial, 
end


end comm_ring