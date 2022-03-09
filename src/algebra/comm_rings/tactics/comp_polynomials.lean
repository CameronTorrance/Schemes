import algebra.comm_rings.basic

universe u

namespace comm_ring


/-
  The following data type represents polynomials

  const c : c
  pinj k₁ q(x1,...,x(n -(n- k₁ -1)))    : q viewed as polynomial of n vars
  px q(x1, ... xn) k₂ p(x1, ...,x(n-1)) : q(x1,..,xn)xn^(k₂+1) + p.

  k₁ is called the inductive index.
  k₂ is called the power index.
-/

inductive pol (R : Type u)
| const  : R → pol
| pinj   : ℕ → pol → pol 
| px     : pol → ℕ → pol → pol 


/-

-/

end comm_ring 