import algebra.comm_rings.basic

namespace comm_ring

universes u v

structure mul_closed_set (R : Type u) [comm_ring R] : Type u :=
  (body : set R)
  (contains_one : (1:R) ∈ body)
  (mul_closed : ∀ s₁ s₂, s₁ ∈ body → s₂ ∈ body → (s₁ * s₂) ∈ body)

instance mul_closed_set_coe (R : Type u) [comm_ring R] : has_coe (mul_closed_set R) (set R)
  := ⟨λ S, S.body⟩

structure mcs_type {R: Type u} [comm_ring R] (S : mul_closed_set R) : Type u :=
  (val : R)
  (property : val ∈ S.body)

instance mcs_as_type {R: Type u} [comm_ring R] 
  : has_coe_to_sort (mul_closed_set R) (Type u) := ⟨mcs_type⟩ 

instance mcs_val {R: Type u} [comm_ring R] {S: mul_closed_set R} : has_coe S R := ⟨λ s : S, s.val⟩

def mcs_mul {R: Type u} [comm_ring R] {S: mul_closed_set R} : S → S → S :=
begin
  intros s₁ s₂,
  split,
  apply S.mul_closed,
  exact s₁.property,
  exact s₂.property,
end

instance mcs_has_mul {R: Type u} [comm_ring R] {S: mul_closed_set R} : has_mul S := ⟨mcs_mul⟩ 


@[simp]
lemma mcs_mul_coe {R: Type u} [comm_ring R] {S: mul_closed_set R} : ∀ s₁ s₂ : S, ↑(s₁ * s₂) = (↑s₁) * (↑s₂ :R) := λ _ _,rfl

def equal_as_fractions {R: Type u} [comm_ring R] {S: mul_closed_set R} : R × S → R × S → Prop :=
  λ  p₁ p₂,  ∃ (s : S), ↑s * (p₁.1 * p₂.2 + -(p₂.1 * p₁.2)) = 0

lemma equal_as_fractions_refl {R: Type u} [comm_ring R] {S: mul_closed_set R} : ∀ f : R × S, equal_as_fractions f f :=
begin
  intro f,
  existsi (⟨(1:R),S.contains_one⟩ : S),
  rw [minus_inverse,mul_zero],
end

lemma equal_as_fractions_symm {R: Type u} [comm_ring R] {S : mul_closed_set R} 
  : ∀ f g : R × S, equal_as_fractions f g → equal_as_fractions g f :=
begin
  intros f g hfg,
  cases hfg with s hs,
  existsi s,
  rw [← minus_minus (g.fst * ↑f.snd),← minus_dis,add_comm],
  rw [mul_comm,← minus_mul,mul_comm,hs,minus_zero_zero],
end

lemma equal_as_fractions_trans {R: Type u} [comm_ring R] {S : mul_closed_set R}
  : ∀ f₁ f₂ f₃ : R × S, equal_as_fractions f₁ f₂ → equal_as_fractions f₂ f₃ → equal_as_fractions f₁ f₃ :=
begin
  intros f₁ f₂ f₃ hf₁f₂ hf₂f₃,
  cases f₁ with r₁ s₁,
  cases f₂ with r₂ s₂,
  cases f₃ with r₃ s₃,
  cases hf₁f₂ with s₁₂ hs₁₂,
  simp at hs₁₂,
  cases hf₂f₃ with s₂₃ hs₂₃,
  simp at hs₂₃,
  existsi s₁₂ * s₂₃ * s₂,
  simp,
  have hrw : ↑((s₁₂ * s₂₃) * s₃) * (r₁ * s₂ + - r₂ * s₁) + ↑ ((s₁₂ * s₂₃) * s₁) * (r₂ * s₃ + - r₃ * s₂) =
      ↑s₁₂ * ↑s₂₃ * ↑s₂ * (r₁ * ↑s₃ + - (r₃ * ↑s₁)),
    simp,
    let α : R := ↑s₁₂ * ↑s₂₃,
    have trv : ↑s₁₂ * ↑s₂₃ = α := rfl,
    rw trv,
    have hrw₁ : α * ↑s₃ * (r₁ * ↑s₂ + - r₂ * ↑s₁) = (α * ↑s₂) * (r₁ * ↑s₃) + -r₂ * (α * s₃ * s₁),
      rw mul_comm (-r₂) (α * ↑s₃ * ↑s₁),
      rw [← mul_assoc α,← mul_assoc α,← mul_assoc α,← mul_assoc α],
      rw ← mul_dis α ,
      rw [mul_assoc ↑s₂, mul_comm (↑s₂ * r₁)],
      rw [← mul_assoc ↑s₃ ↑s₁,← mul_dis ↑s₃],
      simp [mul_comm],
    have hrw₂ : α * ↑s₁ * (r₂ * ↑s₃ + - r₃ * ↑s₂) = r₂ * (α * s₃ * s₁) + - (α * ↑s₂) * (r₃ * ↑s₁),
      rw mul_comm r₂ (α * s₃ * s₁),
      rw [mul_comm α s₂,minus_mul,mul_comm (-↑s₂) α],
      rw [← mul_assoc α,← mul_assoc α,← mul_assoc α,← mul_assoc α],
      rw ← mul_dis α,
      rw [mul_assoc (-↑s₂), mul_comm ((-↑s₂) * r₃)],
      rw [mul_comm ↑s₃ ↑s₁, ← mul_assoc ↑s₁,← mul_dis ↑s₁],
      rw [← minus_mul,← minus_mul],
      simp [mul_comm],
    rw [hrw₁,hrw₂],
    rw [← minus_mul,← minus_mul],
    let β₁: R := α * ↑s₂ * (r₁ * ↑s₃),
    have hβ₁ : α * ↑s₂ * (r₁ * ↑s₃) = β₁ := rfl,
    let β₂ : R := r₂ * (α * ↑s₃ * ↑s₁),
    have hβ₂ : r₂ * (α * ↑s₃ * ↑s₁) = β₂ := rfl,
    let β₃ : R := α * ↑s₂ * (r₃ * ↑s₁),
    have hβ₃ : α * ↑s₂ * (r₃ * ↑s₁) = β₃ := rfl,
    rw [hβ₁,hβ₂,hβ₃],
    have hrw₃ : β₁ + -β₂ + (β₂ + -β₃) = β₁ + (-β₂ + β₂) + -β₃,
      simp [add_assoc],
    rw hrw₃,
    rw [add_comm (-β₂),minus_inverse, add_zero],
    rw mul_dis,
    rw [hβ₁, mul_comm (α * ↑s₂), ← minus_mul, mul_comm (r₃ * ↑s₁)],
  rw ← hrw,
  rw [← minus_mul, ← minus_mul],
  let δ₁₂ := r₁ * ↑s₂ + -(r₂ * ↑s₁),
  have hδ₁₂ : r₁ * ↑s₂ + -(r₂ * ↑s₁) = δ₁₂ := rfl,
  let δ₂₃ := r₂ * ↑s₃ + - (r₃ * ↑s₂),
  have hδ₂₃ : r₂ * ↑s₃ + - (r₃ * ↑s₂) = δ₂₃ := rfl,
  rw [hδ₁₂,hδ₂₃],
  rw hδ₁₂ at hs₁₂,
  rw hδ₂₃ at hs₂₃,
  simp,
  clear hrw hδ₁₂ hδ₂₃,
  have hz₁ : ↑s₁₂ * ↑s₂₃ * ↑s₁ * δ₂₃ = 0,
    rw mul_comm ↑s₁₂,
    rw mul_comm,
    rw mul_assoc,
    rw mul_assoc,
    rw mul_comm δ₂₃,
    rw hs₂₃,
    repeat {
      rw mul_comm (0:R),
      rw mul_zero,
    },
  have hz₂ : ↑s₁₂ * ↑s₂₃ * ↑s₃ * δ₁₂ = 0,
    rw ←mul_assoc,
    rw ← mul_assoc,
    rw mul_comm ↑s₁₂,
    rw ← mul_assoc,
    rw ← mul_assoc,
    rw mul_comm δ₁₂,
    rw hs₁₂,
    simp [mul_zero],
  rw [hz₁,hz₂,add_zero],
end



end comm_ring