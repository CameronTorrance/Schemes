import misc.zorns_lemma
import misc.prop
import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import algebra.comm_rings.ideals.order
import algebra.comm_rings.instances.quotient_ring

namespace comm_ring

universe u

open set

def nilpotent {R : Type u} [comm_ring R] (r : R) : Prop := ∃ n : ℕ, r^(nat.succ n) = 0

lemma prime_ideal_power_mem (R : Type u) [comm_ring R] (p : Spec R) : 
  ∀ {r : R} {n : ℕ}, r^n.succ ∈ p.body → r ∈ p.body :=
begin
  intros r n hr,
  induction n with n hn,
  rw power_of_one at hr,
  exact hr,
  cases p.prime r (r^n.succ) hr,
  exact h,
  apply hn,
  exact h,
end 

def nilradical (R : Type u) [comm_ring R] : ideal R
  := ⋂₀ (image (λ p : Spec R, p) (@univ (Spec R)))

lemma nilpotents_in_all_prime_ideals {R : Type u} [comm_ring R] : ∀ {x : R} (p : Spec R), 
  nilpotent x → x ∈ p.body :=
begin
  intros x p hx,
  cases hx with n hx,
  have h : x^n.succ ∈ p.body,
    rw hx,
    exact p.contains_zero,
  apply prime_ideal_power_mem,
  exact h,
end

lemma not_nilpotent_not_zero {R : Type u} [comm_ring R] : ∀ {f : R}, ¬(nilpotent f) → f ≠ 0 :=
begin
  intros f hf ab,
  apply hf,
  existsi 0,
  rw ab,
  rw power_of_one,
end

namespace not_nilpotent_not_in_some_prime_ideal

variables {R : Type u} [comm_ring R] {f : R}

private def no_pows_of_f (hf : ¬ (nilpotent f))
  : set (ideal R) := λ I : ideal R, ∀ n : ℕ, f^n.succ ∉ I.body


private lemma no_pows_of_f_implies_proper {hf : ¬ (nilpotent f)} {I : ideal R} 
  : no_pows_of_f hf I → is_proper I :=
begin
  intro hraw,
  have hf : f ∉ ↑I,
    have trv : f^1 = f := power_of_one f,
    rw ← trv,
    apply hraw,
  intro ab₁,
  rw ab₁ at hf,
  apply hf,
  trivial,
end

private def cvrt {hf : ¬ (nilpotent f)} : subtype (no_pows_of_f hf) → proper_ideal R 
| ⟨I,hI⟩ := ideal_to_proper (no_pows_of_f_implies_proper hI)

private def helper_le (hf : ¬ (nilpotent f)) 
  : subtype (no_pows_of_f hf) → subtype (no_pows_of_f hf) → Prop 
| J₁ J₂:= J₁.val.body ⊆ J₂.val.body

private def no_pows_of_f_has_le (hf : ¬ (nilpotent f)) : has_le (subtype (no_pows_of_f hf))
 := ⟨helper_le hf⟩

local attribute [instance] no_pows_of_f_has_le

private lemma cvrt_body_eq {hf : ¬ (nilpotent f)} : ∀ J : subtype (no_pows_of_f hf), (cvrt J).body = J.val.body
  | ⟨I,hI⟩ := rfl

private lemma cvrt_equal {hf : ¬ (nilpotent f)} :  
  ∀ J₁ J₂ : subtype (no_pows_of_f hf), J₁ = J₂ ↔ cvrt J₁ = cvrt J₂ :=
begin
  intros J₁ J₂,
  split,
  intro h,
  rw h,
  intro h,
  apply val_injective,
  apply ideal_equality,
  simp [← cvrt_body_eq],
  rw h,
end

private lemma cvrt_le {hf : ¬ (nilpotent f)} :  
  ∀ J₁ J₂ : subtype (no_pows_of_f hf), J₁ ≤ J₂ ↔ cvrt J₁ ≤ cvrt J₂ :=
begin
  intros J₁ J₂,
  split,
  intro h,
  suffices h₁ : (cvrt J₁).body ⊆ (cvrt J₂).body,
  exact h₁,
  rw cvrt_body_eq,
  rw cvrt_body_eq,
  exact h,
  intro h,
  have process : (cvrt J₁).body ⊆ (cvrt J₂).body := h,
  rw cvrt_body_eq at process,
  rw cvrt_body_eq at process,
  exact process,
end

private lemma helper_le_refl {hf : ¬ (nilpotent f)} 
  : ∀ J : subtype (no_pows_of_f hf), J ≤ J :=
begin
  intro J,
  rw cvrt_le,
  exact le_refl (cvrt J),
end

private lemma helper_le_trans {hf : ¬ (nilpotent f)} 
  : ∀ J₁ J₂ J₃ : subtype (no_pows_of_f hf), (J₁ ≤ J₂) → (J₂ ≤ J₃) → (J₁ ≤ J₃) :=
begin
  intros J₁ J₂ J₃,
  simp [cvrt_le],
  exact le_trans,
end

private lemma helper_le_anti_symm {hf : ¬ (nilpotent f)} 
  : ∀ J₁ J₂ : subtype (no_pows_of_f hf), J₁ ≤ J₂ → J₂ ≤ J₁ → J₁ = J₂ :=
begin
  intros J₁ J₂,
  simp [cvrt_equal,cvrt_le],
  exact le_antisymm,
end

private def no_pows_of_f_poset {hf : ¬ (nilpotent f)} : partial_order (subtype (no_pows_of_f hf)) :=
begin
  split,
  exact helper_le_anti_symm,
  exact helper_le_refl,
  exact helper_le_trans,
end

local attribute [instance] no_pows_of_f_poset 

private lemma cvrt_chain {hf : ¬(nilpotent f)} {s : set (subtype (no_pows_of_f hf))} : is_chain s → is_chain (image cvrt s) :=
begin
  intros hs x y hxy,
  cases hxy with hx hy,
  cases hx with x₀ hx₀,
  cases hx₀ with hx₀ins hx₀rw,
  cases hy with y₀ hy₀,
  cases hy₀ with hy₀ins hy₀rw,
  simp [← hx₀rw, ← hy₀rw, ←cvrt_le],
  apply hs,
  exact ⟨hx₀ins,hy₀ins⟩, 
end

private def chain_upper_bound {hf : ¬(nilpotent f)} {s : set (subtype (no_pows_of_f hf))} (hs : is_chain s) (ns : s ≠ ∅) : ideal R 
  := proper_ideals_are_ideals (union_of_chain_of_ideals (cvrt_chain hs) (not_empty_image_not_empty cvrt ns))

private lemma no_pow_of_f_chain_upper_bound  {hf : ¬(nilpotent f)} {s : set (subtype (no_pows_of_f hf))} (hs : is_chain s) (ns : s ≠ ∅) 
  : no_pows_of_f hf (chain_upper_bound hs ns) :=
begin
  intros n ab,
  cases ab with A hA,
  cases hA with hAinIm hfninA,
  cases hAinIm with I hI,
  cases hI with hIinIm hIrw,
  simp at hIrw,
  cases hIinIm with J hJ,
  cases hJ with hJins hJrw,
  rw ← hIrw at hfninA,
  rw ← hJrw at hfninA,
  rw cvrt_body_eq at hfninA,
  have h := J.property n,
  apply h,
  assumption, 
end

private lemma chain_upper_bound_upper_bound {hf : ¬(nilpotent f)} {C : set (subtype (no_pows_of_f hf))} (hC : is_chain C) (nC : C ≠ ∅)
  : bounds_subset C ⟨(chain_upper_bound hC nC), no_pow_of_f_chain_upper_bound hC nC⟩ :=
begin
  intros J hJ,
  rw cvrt_le,
  intros x hx,
  simp [cvrt_body_eq],
  existsi (cvrt J).body,
  split,
  existsi cvrt J,
  split,
  existsi J,
  exact ⟨hJ,rfl⟩,
  refl,
  assumption,
end

private def zero_ideal_no_f (hf : ¬(nilpotent f)) : subtype (no_pows_of_f hf) :=
begin
  existsi zero_ideal R,
  intros n ab,
  apply hf,
  existsi n,
  apply zero_ideal_is_just_zero,
  assumption,
end

private lemma maximal_no_pow_f_prime {hf : ¬(nilpotent f)} {J : subtype (no_pows_of_f hf)} 
  : maximal_element J → is_prime (cvrt J) := 
begin
  intros hJ x y,
  apply contrapostive,
  rw not_or_and_not_eqv,
  simp [cvrt_body_eq],
  intro hxy,
  cases hxy with hx hy,
end

lemma thm (hf : ¬(nilpotent f)) : ∃ p : Spec R, f ∉ p.body := 
begin
  have hmaxnof : ∃ J : subtype (no_pows_of_f hf) , maximal_element J,
    apply zorns_lemma,
    intros C hC,
    by_cases C = ∅,
    existsi zero_ideal_no_f hf,
    intros x hx,
    rw h at hx,
    exact false.elim hx,
    existsi (⟨(chain_upper_bound hC h), no_pow_of_f_chain_upper_bound hC h⟩ : subtype (no_pows_of_f hf)),
    exact chain_upper_bound_upper_bound hC h,
  cases hmaxnof with J hJ,
  existsi proper_to_prime (maximal_no_pow_f_prime hJ),
  have trv : (proper_to_prime (maximal_no_pow_f_prime hJ)).body = (cvrt J).body := rfl,
  rw trv,
  rw cvrt_body_eq,
  have res := J.property 0,
  rw power_of_one at res,
  assumption,
end

end not_nilpotent_not_in_some_prime_ideal

end comm_ring