import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import misc.set

universes u 

namespace comm_ring

lemma product_in_product_of_ideals {R : Type u} [comm_ring R] {I₁ I₂ : ideal R} 
  : ∀ {x y : R}, x ∈ I₁.body → y ∈ I₂.body → (x * y) ∈ (I₁ * I₂).body :=
begin
  intros x y hx hy,
  apply linear_combination.add_term,
  exact hx,
  exact hy,
  apply linear_combination.empty_sum,
  rw add_zero,
end

lemma product_of_ideal_extension {R : Type u} [comm_ring R] {I : ideal R}
  : ∀ {x y : R}, ((I + princple_ideal x) * (I + princple_ideal y)).body ⊆ (I + princple_ideal (x * y)).body :=
begin
  intros x y z hz,
  induction hz with z s₁ s₂ l hs₁ hs₂ hlcom hz hl,
  apply ideal.contains_zero,
  rw hz,
  apply ideal.add_closure,
  cases hs₁ with i₁ rest,
  cases rest with int₁ rest,
  cases rest with hi₁ hint₁,
  cases hint₁ with prin₁ hrw₁,
  cases (elements_of_princple_ideal prin₁) with a₁ ha₁,
  cases hs₂ with i₂ rest,
  cases rest with int₂ rest,
  cases rest with hi₂ hint₂,
  cases hint₂ with prin₂ hrw₂,
  cases (elements_of_princple_ideal prin₂) with a₂ ha₂,
  rw [hrw₁,hrw₂,ha₁,ha₂],
  rw mul_dis,
  apply ideal.add_closure,
  apply ideal.mul_absorb,
  existsi i₂,
  existsi (0:R),
  split,
  exact hi₂,
  split,
  apply ideal.contains_zero,
  rw add_zero,
  rw [mul_comm,mul_dis],
  apply ideal.add_closure,
  apply ideal.mul_absorb,
  existsi i₁,
  existsi (0:R),
  split,
  exact hi₁,
  split,
  apply ideal.contains_zero,
  rw add_zero,
  existsi (0: R),
  existsi (a₁*a₂) *(x*y),
  split,
  exact I.contains_zero,
  split,
  apply princple_ideal_membership,
  existsi (a₁ * a₂),
  refl,
  rw [add_comm,add_zero],
  rw mul_assoc,
  rw mul_comm,
  rw ← mul_comm y,
  rw mul_assoc,
  rw mul_assoc,
  rw mul_comm,
  rw mul_comm,
  rw mul_comm a₁ a₂,
  rw mul_comm (a₂ * a₁),
  simp [mul_assoc],
  exact hl,
end

lemma ideal_extension_proper {R : Type u} [comm_ring R] {I : ideal R} {x : R} 
  : x ∉ I.body → I + princple_ideal x ≠ I :=
begin
  intro hxninI,
  intro ab,
  apply hxninI,
  rw ← ab,
  existsi (0:R),
  existsi (x:R),
  split,
  apply ideal.contains_zero,
  split,
  apply princple_ideal_membership,
  existsi (1:R),
  rw [mul_comm,mul_one],
  rw [add_comm,add_zero],
end

lemma proper_ext_ideal_not_mem {R : Type u} [comm_ring R] {I : ideal R} {x : R} 
  : I + princple_ideal x ≠ I → x ∉ I.body :=
begin
  intro hpropex,
  intro ab,
  apply hpropex,
  apply ideal_equality,
  apply set.subset_antisymmetric,
  split,
  intros y hy,
  cases hy with i₁ rest,
  cases rest with i₂ rest,
  cases rest with hi₁ rest,
  cases rest with hi₂ hrw,
  rw hrw,
  apply ideal.add_closure,
  exact hi₁,
  cases elements_of_princple_ideal hi₂,
  rw h,
  apply ideal.mul_absorb,
  exact ab,
  intros y hy,
  existsi y, 
  existsi (0:R),
  split,
  exact hy,
  split,
  apply ideal.contains_zero,
  rw add_zero,
end

end comm_ring