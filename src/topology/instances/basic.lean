import topology.basic


namespace topology

universe u 

open set
open classical

def subspace_is_open {X : Type u} [T_X: topology X] (S : set X) : set (subtype S) → Prop 
  := λ W , ∃ U : set X, is_open U ∧ (include_subset W = U ∩ S)

theorem subspace_whole_space_open {X : Type u} [T_X : topology X] (S : set X) : subspace_is_open S univ :=
begin
  existsi univ,
  split,
  exact T_X.whole_space_open,
  rw include_univ_is_set,
  symmetry,
  exact intersection_subset set_subset_of_univ,
end

theorem subspace_empty_set_open {X : Type u} [T_X : topology X] (S : set X) : subspace_is_open S ∅ :=
begin
  existsi ∅,
  split,
  exact T_X.empty_set_open,
  rw include_empty_is_empty,
  symmetry,
  apply intersection_empty_set,
end

theorem subspace_abitary_unions_open {X : Type u} [T_X : topology X] (S : set X) (C: set (set (subtype S))) 
  : (∀ t, t ∈ C → subspace_is_open S t) → subspace_is_open S (⋃₀ C) :=
begin
  intro all_s_open,
  let U : Π {W: set (subtype S)} (hW : W ∈ C), set X := λ W hW ,some (all_s_open W hW),
  have hU : ∀ {W: set (subtype S)} (hW : W ∈ C), is_open (U hW) ∧ (include_subset W = (U hW) ∩ S) := λ W hW, (some_spec (all_s_open W hW)),
  let UC : set (set X) := λ A, ∃ (W : set (subtype S)) (hW : W ∈ C), A = U hW, 
  existsi ⋃₀ UC,
  split,
  apply T_X.arbitary_unions_open,
  intros W hW,
  cases hW with W_ghost hW,
  cases hW with hW_ghost hW,
  rw hW,
  exact and.left (hU hW_ghost),
  rw ← include_set_prevs_union C,
  rw intersection_dis_over_union,
  have hrw : image include_subset C = image (λ B, B ∩ S) UC, 
    apply subset_antisymmetric,
    split,
    intros A hA,
    cases hA with Ag hAg,
    cases hAg with hAginC hAg,
    have h₁ : U hAginC ∈ UC,
      split,
      existsi hAginC,
      refl,
    existsi (U hAginC),
    split,
    exact h₁,
    rw and.right (hU hAginC) at hAg,
    rw ← hAg,
    intros A hA,
    cases hA with B hB,
    cases hB with hBinUC hBSisA,
    cases hBinUC with W hW,
    cases hW with hWinC hB,
    rw hB at hBSisA,
    simp at hBSisA,
    have h := and.right (hU hWinC),
    rw hBSisA at h,
    rw ← h,
    apply image_membership,
    exact hWinC,
  rw hrw,
end

theorem subspace_pairwise_inters_open {X : Type u} [T_X : topology X] (S : set X) 
  : ∀ s t : set (subtype S), subspace_is_open S s → subspace_is_open S t → subspace_is_open S (s ∩ t) :=
begin
  intros s t hs ht,
  cases hs with Us hs,
  cases ht with Ut ht,
  existsi (Us ∩ Ut),
  split,
  apply T_X.pairwise_inters_open,
  exact and.left hs,
  exact and.left ht,
  rw include_set_prevs_pair_intersection,
  rw [and.right hs, and.right ht],
  rw intersection_commuative Ut S,
  have hrw : Us ∩ S ∩ (S ∩ Ut) = Us ∩ (S ∩ S) ∩ Ut,
    simp [intersection_assoc],
  rw hrw,
  rw set_int_set_set,
  rw ← intersection_assoc,
  rw intersection_commuative S Ut,
  simp [intersection_assoc],
end
 
instance subspace_topology (X : Type u) [T_X : topology X] (S : set X) : topology (subtype S) := 
begin
  split,
  exact subspace_whole_space_open S,
  exact subspace_empty_set_open S,
  exact subspace_abitary_unions_open S,
  exact subspace_pairwise_inters_open S,
end
structure closed_topology (X : Type u) :=
  (closed_b : set X → Prop)
  (whole_space_closed : closed_b univ)
  (empty_set_closed : closed_b ∅)
  (arbitary_inters_closed (s: set (set X)) : (∀ t : set X, t ∈ s → closed_b t) → closed_b (⋂₀ s))
  (pairwise_unions_open : ∀ s t : set X, closed_b s → closed_b t → closed_b (s ∪ t))

def from_closed_topology (X : Type u) (ct : closed_topology X) : topology X :=
{
  is_open := λ S, ct.closed_b (univ \ S),
  empty_set_open :=
    begin
      rw empty_set_diff,
      apply ct.whole_space_closed,
    end,
  whole_space_closed :=
    begin
      rw diff_of_univ_empty,
      apply ct.empty_set_closed,
    end,
  arbitary_unions_open :=
    begin
      intros C hC,
      rw deMorgenUnion,
      apply ct.arbitary_inters_closed,
      intros S hS,
      cases hS with A hA,
      cases hA with AinC Arw,
      rw ← Arw,
      apply hC,
      exact AinC,
    end,
  pairwise_inters_open :=
    begin
      intros U₁ U₂ hU₁ hU₂,
      rw ← sinter_to_inter,
      rw deMorgenInter,
      
    end,
}





end topology