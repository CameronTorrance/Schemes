#print prefix function

universes u v 

namespace function

#print prefix function

open classical


theorem injective_has_left_inverse {X :Type u} [inhabited X] {Y : Type v}  {f : X → Y} 
  : injective f → has_left_inverse f :=
begin
  intro hf,
  sorry,
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
  intro,
  have hfinj := left_inverse.injective hg₂,
  have hfsur := right_inverse.surjective hg₁,
 

end


end function