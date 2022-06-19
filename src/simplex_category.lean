import algebraic_topology.simplex_category
import category_theory.arrow
import category_theory.discrete_category
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.limits.presheaf
import category_theory.limits.preserves.shapes.equalizers

open category_theory

noncomputable theory

open_locale simplicial

universe u

variables {m n : ℕ}
variables {i j k : fin (n + 2)}

lemma hole_decomposition {X} (f : X ⟶ [n + 1]) (h : i ∉ set.range f.to_order_hom)
  : ∃ f', f = f' ≫ simplex_category.δ i :=
begin
  simp only [simplex_category.δ, simplex_category.hom.comp, simplex_category.mk_hom, simplex_category.small_category_comp,
    simplex_category.hom.to_order_hom_mk, set.mem_range, not_exists] at *,
  cases lt_or_eq_of_le (fin.le_last i),

  case or.inl : h' {
    set j := i.cast_pred,
    have hj : i = j.cast_succ := by rwa [fin.cast_succ_cast_pred],
    fconstructor,
    apply simplex_category.hom.mk,
    dsimp at *,
    exact order_hom.comp ⟨j.pred_above, fin.pred_above_right_monotone _⟩ f.to_order_hom,
    dsimp [simplex_category.δ],
    ext1, ext1, ext1,
    simp only [simplex_category.hom.to_order_hom_mk, order_hom.comp_coe, order_embedding.to_order_hom_coe, order_hom.coe_fun_mk,
      function.comp_app],
    set y := f.to_order_hom x with hy,
    simp_rw [←hy, hj],
    rw [fin.cast_pred_cast_succ],
    rw [fin.succ_above_pred_above],
    rw [hy, ←hj],
    apply h,
  },

  case or.inr : h' {
    fconstructor,
    apply simplex_category.hom.mk,
    exact order_hom.comp ⟨fin.cast_pred, fin.cast_pred_monotone⟩ f.to_order_hom,
    ext1, ext1, ext1,
    simp only [h', simplex_category.hom.to_order_hom_mk, order_hom.comp_coe, order_embedding.to_order_hom_coe, order_hom.coe_fun_mk,
      function.comp_app],
    set y := f.to_order_hom x with ←hy,
    simp_rw [hy],
    dsimp,
    rw [fin.succ_above_last],
    rw [fin.cast_succ_cast_pred],
    cases lt_or_eq_of_le (fin.le_last y),
    assumption,
    exfalso,
    specialize h x,
    simp_rw [h', h_1] at *,
    contradiction,
  }
end

@[irreducible]
lemma hole_decomposition' {X} (f : X ⟶ [n + 1]) (h : i ∉ set.range f.to_order_hom)
  : { f' // f = f' ≫ simplex_category.δ i } :=
begin
  have h' := hole_decomposition f h,
  fconstructor,
  exact classical.some h',
  exact classical.some_spec h',
end

def δ_cancel {X} {i} {f g : X ⟶ [n]}
  (h : f ≫ simplex_category.δ i = g ≫ simplex_category.δ i) : f = g :=
begin
  cases lt_or_eq_of_le (fin.le_last i),

  case or.inl : h' {
    let j := i.cast_pred,
    have hj : i = j.cast_succ := by rwa [fin.cast_succ_cast_pred],
    clear_value j,
    subst hj, clear h',
    let h' := congr_arg (λ x, x ≫ simplex_category.σ j) h,
    unfold at h',
    simp_rw [category.assoc', simplex_category.δ_comp_σ_self] at h',
    simp only [simplex_category.hom.comp, simplex_category.hom.id, simplex_category.small_category_id,
      simplex_category.small_category_comp, simplex_category.hom.to_order_hom_mk, order_hom.id_comp,
      simplex_category.hom.mk_to_order_hom] at h',
    assumption,
  },

  case or.inr : h' {
    subst h',
    let h' := congr_arg (λ x, x ≫ simplex_category.σ (fin.last n)) h,
    unfold at h',
    have h'' : fin.last (n + 1) = (fin.last n).succ := by simp only [fin.succ_last],
    simp_rw [category.assoc', h'', simplex_category.δ_comp_σ_succ] at h',
    simp only [simplex_category.hom.comp, simplex_category.hom.id, simplex_category.small_category_id,
      simplex_category.small_category_comp, simplex_category.hom.to_order_hom_mk, order_hom.id_comp,
      simplex_category.hom.mk_to_order_hom] at h',
    assumption,
  },
end

def δ_pullback_cone (h : i ≤ j) := limits.pullback_cone.mk (simplex_category.δ i) (simplex_category.δ j) (simplex_category.δ_comp_δ h)

def δ_pullback_morphism_prop₁ {n : ℕ}
  {i j : fin (n + 2)}
  (h : i ≤ j)
  (s : limits.pullback_cone (simplex_category.δ j.succ)
    (simplex_category.δ i.cast_succ))
  : i ∉ set.range s.fst.to_order_hom :=
begin
  intro hi, cases hi,
  have h' := congr_arg (simplex_category.δ j.succ).to_order_hom hi_h,
  have h'' : (simplex_category.δ j.succ).to_order_hom i = i := by {
    simp [simplex_category.δ],
    apply fin.succ_above_below,
    rw fin.cast_succ_lt_iff_succ_le,
    rwa fin.succ_le_succ_iff,
  },
  have hc := s.condition,
  have hc' := congr_arg (order_hom.to_fun) (congr_arg (simplex_category.hom.to_order_hom) hc),
  simp at hc',
  have hc'' := congr_arg (λ f : fin (s.X.len + 1) → fin ([n + 1 + 1].len + 1), f hi_w) hc',
  simp at hc'',
  rw h' at hc'',
  rw [h''] at hc'',
  simp [simplex_category.δ, simplex_category] at hc'',
  fapply fin.succ_above_ne (fin.cast_succ i) _, exact hc''.symm,
end

def δ_pullback_morphism_prop₂ {n : ℕ}
  {i j : fin (n + 2)}
  (h : i ≤ j)
  (s : limits.pullback_cone (simplex_category.δ j.succ)
    (simplex_category.δ i.cast_succ))
  : j ∉ set.range s.snd.to_order_hom :=
begin
  intro hi, cases hi,
  have h' := congr_arg (simplex_category.δ i.cast_succ).to_order_hom hi_h,
  have h'' : (simplex_category.δ i.cast_succ).to_order_hom j = j.succ := by {
    apply fin.succ_above_above,
    exact order_hom_class.mono fin.cast_succ h,
  },
  have hc := s.condition,
  have hc' := congr_arg (order_hom.to_fun) (congr_arg (simplex_category.hom.to_order_hom) hc),
  simp at hc',
  have hc'' := congr_arg (λ f : fin (s.X.len + 1) → fin ([n + 1 + 1].len + 1), f hi_w) hc',
  simp at hc'',
  rw h' at hc'',
  rw [h''] at hc'',
  simp [simplex_category.δ, simplex_category] at hc'',
  fapply fin.succ_above_ne (fin.succ j) _, exact hc'',
end

def δ_pullback (h : i ≤ j) : limits.is_limit (δ_pullback_cone h) :=
begin
  fapply limits.pullback_cone.is_limit_aux',
  intro s,
  have dec₁ := hole_decomposition' s.fst (δ_pullback_morphism_prop₁ h s),
  have dec₂ := hole_decomposition' s.snd (δ_pullback_morphism_prop₂ h s),
  have dec_eq : dec₁.val = dec₂.val := by {
    cases dec₁, cases dec₂, dsimp,
    fapply δ_cancel, exact i,
    fapply δ_cancel, exact j.succ,
    simp_rw [category.assoc],
    nth_rewrite 1 [simplex_category.δ_comp_δ h],
    simp_rw [←category.assoc],
    rw [←dec₁_property, ←dec₂_property],
    exact s.condition,
  },
  fconstructor,
  exact dec₁.val,
  split,
  dsimp only [δ_pullback_cone],
  rw [limits.pullback_cone.mk_fst],
  rw [←dec₁.property],
  split,
  rw [dec_eq],
  dsimp only [δ_pullback_cone],
  rw [limits.pullback_cone.mk_snd],
  rw [←dec₂.property],
  change (∀ {m : s.X ⟶ [n]},
    m ≫ (δ_pullback_cone h).fst = s.fst → m ≫ (δ_pullback_cone h).snd = s.snd → m = dec₁.val),
  dsimp only [δ_pullback_cone],
  simp_rw [limits.pullback_cone.mk_fst, limits.pullback_cone.mk_snd],
  intros m e₁ e₂,
  fapply δ_cancel, exact i,
  rw [e₁, ←dec₁.property],
end
