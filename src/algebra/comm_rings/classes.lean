import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import misc.rationals.pos_nat

open classical

universes u v

namespace comm_ring

/-
  In this file we define various important classes of commuative ring
  to be used elsewhere.
-/

class local_ring (R : Type u) [comm_ring R] :=
  (unquie_maximal_ideal : MaxSpec R)
  (only_one_maximal_ideal : ∀ m : MaxSpec R, m = unquie_maximal_ideal)


class field (R : Type u) [comm_ring R] :=
  (non_zero_implies_unit : ∀ {x : R}, x ≠ 0 → unit x)


end comm_ring