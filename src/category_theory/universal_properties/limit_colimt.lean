import category_theory.basic
import category_theory.instances

universes v vᵢ vₒ u uᵢ uₒ

open classical

namespace category

def filtered_category (C : Type u) [nonempty C] [category.{v} C] : Prop
  := (∀ i₁ i₂ : C, ∃ (j : C), nonempty (Mor i₁ j) ∧ nonempty (Mor i₂ j)) 
      ∧ (∀ (i j : C) (f₁ f₂ : Mor i j), ∃ (k : C) (w : Mor j k), w ∘ₘ f₁ = w ∘ₘ f₂)  

@[reducible]
def is_cocone {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C) 
  : (Σ cl : C, Π i : I, Mor (F.map i) cl) → Prop 
  | ⟨cl ,j⟩ := ∀ (i₁ i₂ : I) (f : Mor i₁ i₂), j i₁ = (j i₂) ∘ₘ (F.fmap f)

def is_colimit {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C) 
  : (Σ cl : C, Π i : I, Mor (F.map i) cl) → Prop := 
  λ cᵤ, is_cocone F cᵤ ∧ ∀ c, is_cocone F c → ∃! φ : Mor cᵤ.1 c.1, ∀ i : I, c.2 i = φ ∘ₘ cᵤ.2 i    

theorem colimits_essentially_unquie {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] {F : I +→ C}
  {cl₁ cl₂ : (Σ cl : C, Π i : I, Mor (F.map i) cl)} (hcl₁ : is_colimit F cl₁) (hcl₂ : is_colimit F cl₂)
  : ∃! φ : Mor cl₁.1 cl₂.1, (isomorphism φ) ∧ (∀ i : I, cl₂.2 i = φ ∘ₘ cl₁.2 i) := 
begin
  cases cl₁ with cl₁ j₁,
  cases cl₂ with cl₂ j₂,
  cases hcl₁.2 ⟨cl₂,j₂⟩ hcl₂.1 with φ hφ,
  dsimp at hφ,
  cases hcl₂.2 ⟨cl₁,j₁⟩ hcl₁.1 with ψ hψ,
  dsimp at hψ,
  cases hcl₁.2 ⟨cl₁,j₁⟩ hcl₁.1 with idcl₁ hidcl₁,
  dsimp at hidcl₁,
  cases hcl₂.2 ⟨cl₂,j₂⟩ hcl₂.1 with idcl₂ hidcl₂,
  dsimp at hidcl₂,
  cases hφ with hφ uφ,
  cases hψ with hψ uψ,
  cases hidcl₁ with hidcl₁ uidcl₁,
  cases hidcl₂ with hidcl₂ uidcl₂,
  have hrw₁ : idₘ cl₁ = idcl₁,
    apply uidcl₁,
    intro,
    rw id_comp_left,
  have hrw₂ : idₘ cl₂ = idcl₂,
    apply uidcl₂,
    intro,
    rw id_comp_left,
  existsi φ,
  split,
  split,
  existsi ψ,
  dsimp,
  split,
  rw hrw₂,
  apply uidcl₂,
  intro,
  rw [←comp_assoc,←hψ,←hφ],
  rw hrw₁,
  apply uidcl₁,
  intro,
  rw [←comp_assoc,←hφ,←hψ],
  exact hφ,
  dsimp,
  intros φ' hφ',
  apply uφ,
  exact hφ'.2,
end


theorem isomorphisms_prev_colimits {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C)
  {c₁: (Σ cl : C, Π i : I, Mor (F.map i) cl)} {c : C} {φ : Mor c₁.1 c} (hφ : isomorphism φ)
  : is_colimit F c₁ → is_colimit F ⟨c, λ i : I, φ ∘ₘ (c₁.2 i)⟩ :=
begin
  intro colc₁,
  cases hφ with ψ hψ,
  cases hψ with hψ₁ hψ₂,
  cases c₁ with c₁ j₁,
  split,
  simp [is_colimit,is_cocone] at colc₁,
  cases colc₁ with c₁cocone c₁uni,
  simp [is_cocone],
  intros i₁ i₂ f,
  rw c₁cocone i₁ i₂ f,
  simp [comp_assoc],
  intros c₂ hc₂,
  cases colc₁ with c₁cocone c₁uni,
  cases c₁uni c₂ hc₂ with ρ hρ,
  cases c₂ with c₂ j₂,
  cases hρ with hρ₁ hρ₂, 
  existsi ρ ∘ₘ ψ,
  split,
  dsimp,
  intro i,
  rw [← comp_assoc, comp_assoc (j₁ i),hψ₂, id_comp_left],
  apply hρ₁,
  intros γ hγ,
  have hrw : γ ∘ₘ φ = ρ,
    apply hρ₂,
    intro i,
    rw ← comp_assoc,
    apply hγ,
  rw [← hrw, ← comp_assoc,hψ₁,id_comp_right],
end 

/-
  Using a nonstandard defintion of concrete category based on the idea
  that I'm only using the defn for sheaf, and need them to commute with
  colimits to define stalks. 

  I say that functor F : C → D commutes with colimits if for all functors
  G : J → C, G has a colimit if and only if F ∘ G has a colimit,
  and the cannoial morphism d → F(c) is an isomorphism where c, d are 
  colimits of G and (F ∘ G) respectively.
-/

def image_of_colimit {C : Type u} [category.{v} C] {D : Type uₒ} [category.{vₒ} D] {J : Type uᵢ} 
  [category.{vᵢ} J] {F : J +→ C} (G : C +→ D) (c : Σ cl : C, Π i : J, Mor (F.map i) cl)
  : Σ d : D, Π i : J, Mor ((G ⊚ F).map i) d := ⟨G.map c.1, λ i : J, G.fmap (c.2 i)⟩ 

theorem image_of_colimit_cocone {C : Type u} [category.{v} C] {D : Type uₒ} [category.{vₒ} D] {J : Type uᵢ} 
  [category.{vᵢ} J] {F : J +→ C} (G : C +→ D) {c : Σ cl : C, Π i : J, Mor (F.map i) cl} (hc : is_colimit F c)
  : is_cocone (G ⊚ F) (image_of_colimit G c) :=
begin
  intros i₁ i₂ f,
  simp,
  have hrw : (G ⊚ F).fmap f = G.fmap (F.fmap f) := rfl,
  cases c,
  rw [hrw,← G.fmap_prevs_comp],
  cases hc,
  simp [is_cocone] at hc_left,
  rw ← hc_left i₁ i₂ f,
end

theorem exists_image_of_colimit_can_mor {C : Type u} [category.{v} C] {D : Type uₒ} [category.{vₒ} D] {J : Type uᵢ} 
  [category.{vᵢ} J] {F : J +→ C} {G : C +→ D} {c : Σ cl : C, Π i : J, Mor (F.map i) cl} 
  {d : Σ dl : D, Π i : J, Mor ((G ⊚ F).map i) dl} (hc : is_colimit F c) (hd : is_colimit (G ⊚ F) d)
  : ∃! φ : Mor d.1 (image_of_colimit G c).1, ∀ i : J, (image_of_colimit G c).2 i = φ ∘ₘ (d.2 i) :=
begin
  cases hd with dcocone duni,
  apply duni,
  apply image_of_colimit_cocone,
  exact hc,
end

noncomputable def image_of_colimit_can_mor {C : Type u} [category.{v} C] {D : Type uₒ} [category.{vₒ} D] {J : Type uᵢ} 
  [category.{vᵢ} J] {F : J +→ C} {G : C +→ D} {c : Σ cl : C, Π i : J, Mor (F.map i) cl} 
  {d : Σ dl : D, Π i : J, Mor ((G ⊚ F).map i) dl} (hc : is_colimit F c) (hd : is_colimit (G ⊚ F) d)
  : Mor d.1 (image_of_colimit G c).1 := some (exists_image_of_colimit_can_mor hc hd)

theorem image_of_colimit_can_mor_property {C : Type u} [category.{v} C] {D : Type vₒ} [category.{vₒ} D] {J : Type uᵢ} 
  [category.{vᵢ} J] {F : J +→ C} {G : C +→ D} {c : Σ cl : C, Π i : J, Mor (F.map i) cl} 
  {d : Σ dl : D, Π i : J, Mor ((G ⊚ F).map i) dl} (hc : is_colimit F c) (hd : is_colimit (G ⊚ F) d)
  : (∀ i : J, (image_of_colimit G c).2 i = (image_of_colimit_can_mor hc hd) ∘ₘ (d.2 i)) ∧ (∀ ϕ : Mor d.1 (image_of_colimit G c).1,
  (∀ i : J, (image_of_colimit G c).2 i = ϕ ∘ₘ (d.2 i)) → ϕ = (image_of_colimit_can_mor hc hd)) 
  := some_spec (exists_image_of_colimit_can_mor hc hd)

structure concrete_category (C : Type u) [category.{v} C] :=
  (val : C +→ Type v)
  (property : faithful_functor val)
  (up_colimits_iff_down_colimits : ∀ {J : Type v} [category.{v} J] [nonempty J] 
  (hJ : filtered_category J) {F : J +→ C},
  (∃ c : (Σ cl : C, Π i : J, Mor (F.map i) cl), is_colimit F c) ↔ 
  (∃ d : (Σ dl : Type v, Π i : J, Mor ((val ⊚ F).map i) dl), is_colimit (val ⊚ F) d))
  (colimit_can_iso : ∀ {J : Type v} [category.{v} J] [nonempty J] 
  (hJ : filtered_category J) {F : J +→ C} {c : Σ cl : C, Π i : J, Mor (F.map i) cl} 
  {d : Σ dl : Type v, Π i : J, Mor ((val ⊚ F).map i) dl} (hc : is_colimit F c) 
  (hd : is_colimit (val ⊚ F) d), isomorphism (image_of_colimit_can_mor hc hd))

theorem set_comp_app : ∀ {A₁ A₂ A₃ : Type u} (f₁ : Mor A₂ A₃) (f₂ : Mor A₁ A₂) (s : A₁), 
  ((f₁ ∘ₘ f₂) : A₁ → A₃) s =  f₁ ( f₂ s) := λ _ _ _ _ _ _, rfl


def f_colim_equiv {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : (Σ i : J, F.map i) → (Σ i : J, F.map i) → Prop  
  | ⟨i₁,s₁⟩ ⟨i₂,s₂⟩ := ∃ (k : J) (f₁ : Mor i₁ k) (f₂ : Mor i₂ k), F.fmap f₁ s₁ = F.fmap f₂ s₂

lemma f_colim_equiv_refl {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : ∀ s : (Σ i : J, F.map i), f_colim_equiv hJ F s s :=
begin
  intro s,
  cases s with i s,
  existsi i,
  existsi idₘ i,
  existsi idₘ i,
  refl,
end

lemma f_colim_equiv_symm {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v): ∀ s₁ s₂ : (Σ i : J, F.map i), f_colim_equiv hJ F s₁ s₂ → f_colim_equiv hJ F s₂ s₁ :=
begin
  intros s₁ s₂ h₁₂,
  cases s₁ with i₁ s₁,
  cases s₂ with i₂ s₂,
  cases h₁₂ with k hk,
  cases hk with f₁ h,
  cases h with f₂ h,
  existsi k,
  existsi f₂,
  existsi f₁,
  symmetry,
  exact h,
end

lemma f_colim_equiv_trans {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : ∀ s₁ s₂ s₃ : (Σ i : J, F.map i), f_colim_equiv hJ F s₁ s₂ → f_colim_equiv hJ F s₂ s₃ 
    → f_colim_equiv hJ F s₁ s₃ :=
begin
  intros s₁ s₂ s₃ h₁₂ h₂₃,
  cases s₁ with i₁ s₁,
  cases s₂ with i₂ s₂,
  cases s₃ with i₃ s₃,
  cases hJ with hbound hcon,
  cases h₁₂ with k₁ rest,
  cases rest with a₁ rest,
  cases rest with a₂ h₁₂,
  cases h₂₃ with k₂ rest,
  cases rest with b₁ rest,
  cases rest with b₂ h₂₃,
  cases hbound k₁ k₂ with k hk,
  cases hk with hk₁ hk₂,
  cases hk₁ with φ₁,
  cases hk₂ with φ₂,
  cases hcon i₂ k (φ₁ ∘ₘ a₂) (φ₂ ∘ₘ b₁) with w hw,
  cases hw with ϕ hϕ,
  existsi w,
  existsi ϕ ∘ₘ φ₁ ∘ₘ a₁,
  existsi ϕ ∘ₘ φ₂ ∘ₘ b₂,
  simp [F.fmap_prevs_comp],
  simp [set_comp_app],
  rw [h₁₂,←h₂₃],
  rw ←set_comp_app (F.fmap φ₁),
  rw ←set_comp_app (F.fmap φ₂),
  simp [← set_comp_app (F.fmap ϕ),← F.fmap_prevs_comp],
  rw hϕ, 
end

def f_colim_equiv_setoid {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : setoid (Σ i : J, F.map i) 
  := ⟨f_colim_equiv hJ F, f_colim_equiv_refl hJ F, f_colim_equiv_symm hJ F, f_colim_equiv_trans hJ F⟩ 

def filtered_colimit_set_obj {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : Type v := quotient (f_colim_equiv_setoid hJ F)

def filtered_colimit_set_mor {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : Π i : J, Mor (F.map i) (filtered_colimit_set_obj hJ F) 
  := λ (i:J) (s : F.map i),  @quotient.mk (Σ i : J, F.map i) (f_colim_equiv_setoid hJ F) ⟨i,s⟩

def filtered_colimit_set {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : (Σ cl : Type v, Π i : J, Mor (F.map i) cl) 
  := ⟨filtered_colimit_set_obj hJ F, filtered_colimit_set_mor hJ F⟩ 

def filtered_colimit_set_pre_can {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  {F : J +→ Type v} {c : (Σ cl : Type v, Π i : J, Mor (F.map i) cl)} (hc : is_cocone F c) 
  : (Σ i : J, F.map i) → c.1
  | ⟨i,s⟩ := (c.2 i) s   

lemma filtered_colimit_set_pre_can_lift {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  {F : J +→ Type v} {c : (Σ cl : Type v, Π i : J, Mor (F.map i) cl)} (hc : is_cocone F c) 
  : ∀ s₁ s₂ : (Σ i : J, F.map i), f_colim_equiv hJ F s₁ s₂ → 
  filtered_colimit_set_pre_can hJ hc s₁ = filtered_colimit_set_pre_can hJ hc s₂ :=
begin 
  intros s₁ s₂,
  intro h₁₂,
  cases s₁ with i₁ s₁,
  cases s₂ with i₂ s₂,
  simp [filtered_colimit_set_pre_can],
  cases c with c j,
  simp,
  simp [is_cocone] at hc,
  cases h₁₂ with k hk,
  cases hk with f₁ rest,
  cases rest with f₂ h₁₂,
  rw [hc i₁ k f₁, hc i₂ k f₂],
  simp [set_comp_app],
  rw h₁₂,
end

def filtered_colimit_set_can {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  {F : J +→ Type v} {c : (Σ cl : Type v, Π i : J, Mor (F.map i) cl)} (hc : is_cocone F c) 
  : filtered_colimit_set_obj hJ F → c.1 :=
begin
  apply quotient.lift,
  apply filtered_colimit_set_pre_can_lift,
  assumption,
end

lemma filtered_colimit_set_can_concrete_char {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  {F : J +→ Type v} {c : (Σ cl : Type v, Π i : J, Mor (F.map i) cl)} (hc : is_cocone F c)
  : ∀ (i : J) (s : F.map i), 
  filtered_colimit_set_can hJ hc (@quotient.mk (Σ i : J, F.map i) (f_colim_equiv_setoid hJ F) ⟨i,s⟩) = c.2 i s :=
begin
  intros i s,
  refl,
end

theorem filtered_colimit_set_colimit {J : Type v} [category.{v} J] [nonempty J] (hJ : filtered_category J)
  (F : J +→ Type v) : is_colimit F (filtered_colimit_set hJ F) :=
begin
  have trv₁ : (filtered_colimit_set hJ F).2 = filtered_colimit_set_mor hJ F := rfl,
  split,
  intros i₁ i₂ f,
  simp [filtered_colimit_set_mor],
  apply funext,
  intro s,
  rw set_comp_app,
  apply quotient.sound,
  existsi i₂,
  existsi f,
  existsi idₘ i₂,
  rw functor.fmap_prevs_id,
  refl,
  intros c hc,
  existsi filtered_colimit_set_can hJ hc,
  cases c with c j,
  simp [trv₁,filtered_colimit_set_mor],
  split,
  intro i,
  apply funext,
  intro s,
  rw set_comp_app,
  rw filtered_colimit_set_can_concrete_char hJ hc,
  intros ψ hψ,
  apply funext,
  intro q,
  cases (@quotient.exists_rep (Σ i : J, F.map i) (f_colim_equiv_setoid hJ F) q) with r hr,
  cases r with i s,
  simp [←hr],
  rw filtered_colimit_set_can_concrete_char hJ hc,
  simp,
  symmetry,
  rw hψ i,
  refl,
end

theorem concrete_category_has_filtered_colimits {C : Type u} [category.{v} C] {J : Type v} [category.{v} J] 
  [nonempty J] (hJ : filtered_category J) (S : concrete_category C) (F : J +→ C) 
  : ∃ c : (Σ cl : C, Π i : J, Mor (F.map i) cl), is_colimit F c := 
begin
  cases S with S Sfaithful Sexist Scaniso,
  let setcolimit := filtered_colimit_set hJ (S ⊚ F),
  have setcolimit_colimit : is_colimit (S ⊚ F) setcolimit := filtered_colimit_set_colimit hJ (S ⊚ F),
  rw Sexist,
  existsi setcolimit,
  exact setcolimit_colimit,
  exact hJ,
end

noncomputable def filtered_colimit {C : Type u} [category.{v} C] {J : Type v} [category.{v} J] 
  [nonempty J] (hJ : filtered_category J) (S : concrete_category C) (F : J +→ C)
  : (Σ cl : C, Π i : J, Mor (F.map i) cl) 
  := some (concrete_category_has_filtered_colimits hJ S F)

theorem filtered_colimit_property {C : Type u} [category.{v} C] {J : Type v} [category.{v} J] 
  [nonempty J] (hJ : filtered_category J) (S : concrete_category C) (F : J +→ C)
  : is_colimit F (filtered_colimit hJ S F)
  := some_spec (concrete_category_has_filtered_colimits hJ S F)


end category