import algebra.comm_rings.basic

namespace comm_ring

universes u₁ u₂

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

def initial_ring : (Σ R : Type u₁, comm_ring R) → Prop
  | ⟨R,lR⟩ := ∀ pair : (Σ R' : Type u₂, comm_ring R'), ∃! ψ : @ring_hom R pair.1 lR pair.2, true


def int_hom_map (R : Type u₁) [comm_ring R] : ℤ → R
  | (int.of_nat n)          := nat_to_ring R n
  | (int.neg_succ_of_nat n) := -1 + - (nat_to_ring R n)


lemma int_hom_of_nat {R : Type u₁} [comm_ring R] : ∀ {n : ℕ}, int_hom_map R (int.of_nat n) = nat_to_ring R n := λ _, rfl

theorem int_hom_prevs_zero {R : Type u₁} [lR:comm_ring R] : int_hom_map R int.zero = lR.zero := rfl

inductive zero_ring : Type
  | elm : zero_ring

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

end comm_ring