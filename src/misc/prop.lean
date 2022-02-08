universe u

theorem not_or_and_not : ∀ { p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
begin
  intros p q h,
  split,
  intro hp,
  apply h,
  left,
  exact hp,
  intro hq,
  apply h,
  right,
  exact hq,
end 

theorem not_not : ∀ {p : Prop} , ¬¬p → p :=
begin
  intros p nnp,
  by_contradiction,
  exact nnp h,
end

theorem exists_not_of_not_exists {α :Sort u} {p : α → Prop} : (¬(∀ x : α , p x)) → ∃ x : α , ¬(p x) :=
begin
  intro h₁,
  by_contradiction,
  have h₂ := forall_not_of_not_exists h,
  simp at h₂,
  apply h₁,
  intro x,
  apply not_not,
  apply h₂,
end

theorem not_implies (p q : Prop) : ¬ (p → q) ↔ ¬p ∧ q := sorry