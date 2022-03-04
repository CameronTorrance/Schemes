universe u

open classical



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

theorem not_or_and_not_eqv (p q : Prop) : ¬ (p ∨ q) ↔ (¬p) ∧ (¬q) :=
begin
  split,
  intro h,
  split,
  intro hp,
  apply h,
  left,
  exact hp,
  intro hq,
  apply h,
  right,
  exact hq,
  intros h h₁,
  cases h with np nq,
  cases h₁,
  exact np h₁,
  exact nq h₁,
end

theorem implies_or_not (p q : Prop) : p → q ↔ (¬p) ∨ q :=
begin
  split,
  intro hpq,
  by_cases p,
  right,
  exact hpq h,
  left,
  exact h,
  intro h,
  intro hp,
  cases h,
  apply false.elim,
  apply h,
  apply hp,
  exact h,
end

theorem not_not_eqv (p : Prop) : ¬¬ p ↔ p :=
begin
  split,
  apply not_not,
  apply not_not_intro,
end 

theorem not_implies (p q : Prop) : ¬ (p → q) ↔ p ∧ ¬q :=
begin
  rw implies_or_not,
  rw not_or_and_not_eqv,
  rw not_not_eqv,
end

theorem contrapostive (p q : Prop) : (¬q → ¬p) → (p → q) := 
begin
  intros hnqnp hp,
  cases (em q),
  exact h,
  apply false.elim,
  apply hnqnp h,
  exact hp, 
end