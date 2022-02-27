universes u v 

namespace function

open classical

def inverse {X : Type u} {Y : Type v} (g : Y → X) (f : X → Y) := (f ∘ g = id) ∧ (g ∘ f = id)

section

local attribute [instance, priority 10] classical.prop_decidable

theorem injective_has_left_inverse {X :Type u} [inhabited X] {Y : Type v}  {f : X → Y} 
  : injective f → has_left_inverse f :=
begin
  intro hf,
  let g := λ y : Y, if h : ∃ x, f x = y then some h else default,
  let hg  :  Π ( y : Y) ( h : ∃ x, f x = y), f (g y) = y,
    intros y hy,
    simp [g,dif_pos hy,some_spec hy],
  existsi g,
  intro x,
  apply hf,
  apply hg,
  exact ⟨x,rfl⟩,
end

end

theorem surjective_has_right_inverse {X : Type u} {Y : Type v} {f : X → Y}
  : surjective f → has_right_inverse f :=
begin
  intro hf,
  let g := λ y, some (hf y),
  let hg : ∀ y : Y , f (g y) = y := λ y, some_spec(hf y),
  existsi g,
  apply hg,
end

theorem left_inverse_equals_right_inverse {X : Type u} {Y : Type v} {f : X → Y} 
  : ∀ g₁ g₂ : Y → X, right_inverse g₁ f → left_inverse g₂ f → g₁ = g₂ :=
begin
  intros g₁ g₂ hg₁ hg₂,
  apply funext,
  intro y,
  exact calc g₁ y = g₂ (f (g₁ y)) : by rw hg₂
              ... = g₂ y          : by rw hg₁,
end

theorem bijection_has_inverse {X: Type u} {Y : Type v} [inhabited X]{f : X → Y}
  : bijective f → ∃ g : Y → X, inverse g f :=
begin
  intro hf,
  cases hf with finj fsur,
  cases injective_has_left_inverse finj with g₂ hg₂,
  cases surjective_has_right_inverse fsur with g₁ hg₁,
  have hrw : g₁ = g₂,
    apply left_inverse_equals_right_inverse,
    exact hg₁,
    exact hg₂,
  existsi g₁,
  split,
  apply funext,
  apply hg₁,
  rw hrw,
  apply funext,
  apply hg₂,
end

end function