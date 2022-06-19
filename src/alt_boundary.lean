import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import algebraic_topology.simplicial_object
import category_theory.arrow
import category_theory.discrete_category
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.limits.presheaf
import category_theory.limits.preserves.shapes.equalizers

import simplex_category

open category_theory

noncomputable theory

open_locale simplicial

universe u

variable n : ℕ

structure boundary_part :=
  mk :: (i j : fin (n + 2)) (h : i ≤ j)

structure end_part :=
  mk :: (i : fin (n + 3))

def boundary_f (p : boundary_part n) := Δ[n]
def simplex_f (p : end_part n) := Δ[n+1]

def boundary_start := ∐ (boundary_f n)

def simplex_end := ∐ (simplex_f n)

def morph_boundary_1 : boundary_start n ⟶ simplex_end n :=
  limits.sigma.desc
    (λ idx : boundary_part n, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.j.succ⟩))
  
def morph_boundary_2 : boundary_start n ⟶ simplex_end n :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.j)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.i.cast_succ⟩))

def boundary_morphism : simplex_end n ⟶ ∂Δ[n + 2] :=
  limits.sigma.desc (λ b, yoneda_equiv.inv_fun ⟨simplex_category.δ b.i, by {
    simp only [not_exists, not_forall, coe_coe],
    use b.i,
    intros x,
    exact fin.succ_above_ne _ _,
  }⟩)

lemma boundary_coeq : morph_boundary_1 n ≫ boundary_morphism n = morph_boundary_2 n ≫ boundary_morphism n :=
begin
  rewrite [boundary_morphism, morph_boundary_1, morph_boundary_2],
  apply limits.colimit.hom_ext,
  simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
    equiv.inv_fun_as_coe, category.assoc],
  intro idx,
  rw [←equiv.apply_eq_iff_eq yoneda_equiv],
  rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality],
  rw [equiv.apply_symm_apply, equiv.apply_symm_apply],
  dsimp only [sSet.boundary, simplex_category.hom.to_order_hom, coe_coe],
  simp only [quiver.hom.unop_op, subtype.coe_mk],
  cases idx with i j h,
  simp only [function.embedding.to_fun_eq_coe, rel_embedding.coe_fn_to_embedding],
  exact simplex_category.δ_comp_δ h,
end

def boundary_fork := limits.cofork.of_π (boundary_morphism n) (boundary_coeq n)

def boundary_hole {m n} (f : [m] ⟶ [n + 1]) (h : ¬ function.surjective f.to_order_hom)
  : ∃ i, i ∉ set.range f.to_order_hom :=
begin
  simp only [not_forall, not_exists] at h,
  cases h,
  use h_w,
  simpa only [set.mem_range, not_exists],
end

-- def boundary_colim : limits.is_colimit (boundary_fork n) :=
-- begin
--   apply limits.cofork.is_colimit.mk, swap 3,
--   focus {
--     intro s,
--     dsimp [boundary_fork],
--     refine nat_trans.mk _ _,
--     focus {
--       intros X f,
--       let m := X.unop.len,
--       have hX : X = opposite.op [m] := by simp only [simplex_category.mk_len, opposite.op_unop],
--       clear_value m,
--       subst hX,
--       cases f,
--       apply yoneda_equiv.to_fun,
--       dsimp [sSet.standard_simplex] at f_val,
--       refine _ ≫ _,
--       exact Δ[n + 1],
--       apply yoneda_equiv.inv_fun,
--       exact nonsurj_fun f_val f_property,
--       refine _ ≫ s.π,
--       exact limits.sigma.ι (simplex_f n) ⟨nonsurj_index f_val f_property⟩,
--     },
--     focus {
--       intros X Y f,
--       have sn := s.π.naturality f,
--       let m := X.unop.len, let k := Y.unop.len,
--       have hX : X = opposite.op [m] := by simp only [simplex_category.mk_len, opposite.op_unop],
--       have hY : Y = opposite.op [k] := by simp only [simplex_category.mk_len, opposite.op_unop],
--       clear_value m k,
--       subst hX, subst hY,
--       ext1,
--       dsimp [sSet.boundary, sSet.standard_simplex, simplex_end] at *,
--       cases x,
--       simp only [order_hom.comp_id, simplex_category.hom.mk_to_order_hom],
--       have sn' : ∀ x, ((∐ simplex_f n).map f ≫ s.π.app (opposite.op [k])) x
--         = (s.π.app (opposite.op [m]) ≫ s.X.map f) x := by { intro, rw [sn], },
--       simp only [types_comp_apply] at sn',
--       rw ←sn',
--       have cf := limits.cofork.condition s, 
--       dsimp [morph_boundary_1, morph_boundary_2] at cf,
--     },


--     --have df := nonsurj_decomposition f_val f_property,
--   },
-- end
