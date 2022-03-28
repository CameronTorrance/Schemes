import misc.rationals.basic

namespace rational

instance rational_has_neg : has_neg ℚ := ⟨rational_minus⟩
instance rational_has_sub : has_sub ℚ := ⟨λ x y, x + -y⟩  

theorem rational_minus_concrete_char : ∀ (z : ℤ) (n : ℕ⁺), (-⟦(z,n)⟧ : ℚ) = ⟦(-z,n)⟧ := λ _ _, rfl




end rational