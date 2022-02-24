import algebra.comm_rings.basic
import misc.set

namespace comm_ring

universes u v

def Im {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  := subtype (λ y : R₂, ∃ x : R₁, y = φ x) 

def Im_add {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) 
  : Im φ → Im φ → Im φ :=
begin
  intros yu₁ yu₂,
  cases yu₁ with y₁ hy₁,
  cases yu₂ with y₂ hy₂,
  existsi y₁ + y₂,
  cases hy₁ with x₁ hx₁,
  cases hy₂ with x₂ hx₂,
  existsi x₁ + x₂,
  rw [hx₁,hx₂],
  symmetry,
  exact φ.prevs_add x₁ x₂,
end

instance image_add {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : has_add (Im φ) := ⟨Im_add φ⟩ 

def Im_mul {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) 
  : Im φ → Im φ → Im φ :=
begin
  intros yu₁ yu₂,
  cases yu₁ with y₁ hy₁,
  cases yu₂ with y₂ hy₂,
  existsi y₁ * y₂,
  cases hy₁ with x₁ hx₁,
  cases hy₂ with x₂ hx₂,
  existsi x₁ * x₂,
  rw [hx₁,hx₂],
  symmetry,
  exact φ.prevs_mul x₁ x₂,
end

instance image_mul {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : has_mul (Im φ) := ⟨Im_mul φ⟩  

def Im_one {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) : Im φ :=
begin
  existsi (1 : R₂),
  existsi (1 : R₁),
  symmetry,
  exact φ.prevs_one,
end

instance image_one {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) 
  : has_one (Im φ) := ⟨Im_one φ⟩

def Im_zero {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂) : Im φ :=
begin
  existsi (0 : R₂),
  existsi (0 : R₁),
  symmetry,
  exact ring_hom_preserves_zero φ,
end

instance image_zero {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : has_zero (Im φ) := ⟨Im_zero φ⟩

def Im_minus {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : Im φ → Im φ :=
begin
  intro a,
  cases a with y hy,
  existsi -y,
  cases hy with x hx,
  existsi -x,
  symmetry,
  rw hx,
  apply minus_commutes_with_hom,
end

instance Im_neg {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : has_neg (Im φ) := ⟨Im_minus φ⟩ 

theorem Im_add_assoc {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a b c : Im φ, a + (b + c) = (a + b) + c :=
begin
  intros a b c,
  apply set.val_injective,
  cases a,
  cases b,
  cases c,
  exact add_assoc a_val b_val c_val,
end

theorem Im_add_comm {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a b : Im φ, a + b  = b + a :=
begin
  intros a b,
  apply set.val_injective,
  cases a,
  cases b,
  exact add_comm a_val b_val,
end

theorem Im_add_zero {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a : Im φ , a + 0 = a := 
begin
  intro a,
  apply set.val_injective,
  cases a,
  exact add_zero a_val,
end

theorem Im_minus_inverse {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a : Im φ , a + -a = 0 := 
begin
  intro a,
  apply set.val_injective,
  cases a,
  exact minus_inverse a_val,
end

theorem Im_mul_assoc {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a b c : Im φ, a * (b * c) = (a * b) * c :=
begin
  intros a b c,
  apply set.val_injective,
  cases a,
  cases b,
  cases c,
  exact mul_assoc a_val b_val c_val,
end

theorem Im_mul_comm {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a b : Im φ, a * b  = b * a :=
begin
  intros a b ,
  apply set.val_injective,
  cases a,
  cases b,
  exact mul_comm a_val b_val,
end

theorem Im_mul_one {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a : Im φ , a * 1 = a := 
begin
  intro a,
  apply set.val_injective,
  cases a,
  exact mul_one a_val,
end

theorem Im_mul_dis {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : ∀ a b c : Im φ, a * (b + c) = a * b + a * c :=
begin
  intros a b c,
  apply set.val_injective,
  cases a,
  cases b,
  cases c,
  exact mul_dis a_val b_val c_val,
end

instance image_is_ring {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : comm_ring (Im φ) :=
begin
  split,
  exact Im_add_assoc φ,
  exact Im_add_comm φ,
  exact Im_add_zero φ,
  exact Im_minus_inverse φ,
  exact Im_mul_assoc φ,
  exact Im_mul_comm φ,
  exact Im_mul_one φ,
  exact Im_mul_dis φ,
end

def im_trival_hom_in {R₁ : Type u} {R₂ : Type v} [comm_ring R₁] [comm_ring R₂] (φ : R₁ →ᵣ R₂)
  : R₁ →ᵣ Im φ :=
{
  map := 
    by {intro x,
        existsi φ x,
        existsi x,
        refl,},
  prevs_add := 
    by { intros a b,
         apply set.val_injective,
         exact φ.prevs_add a b,},
  prevs_mul := 
    by { intros a b,
         apply set.val_injective,
         exact φ.prevs_mul a b,},
  prevs_one :=
    by { apply set.val_injective,
         exact φ.prevs_one},
}

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