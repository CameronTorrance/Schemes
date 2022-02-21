import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
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

def intersection_of_prime_ideals (R : Type u) [comm_ring R] : ideal R
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
| ⟨I₁,h₁⟩ ⟨I₂,h₂⟩ := I₁.body ⊆ I₂.body

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

lemma thm (hf : ¬ (nilpotent f)) : ∃ p : Spec R, f ∉ p.body := sorry

end not_nilpotent_not_in_some_prime_ideal

end comm_ring