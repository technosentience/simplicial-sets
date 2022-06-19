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
variable k : fin (n + 3)

structure horn_part :=
  mk :: (i j : fin (n + 2)) (h₁ : i ≤ j) (h₂ : i.cast_succ ≠ k) (h₃ : j.succ ≠ k)

structure excluded_part :=
  mk :: (i : fin (n + 3)) (h : i ≠ k)

def horn_f (p : horn_part n k)  := Δ[n]
def excluded_f (p : excluded_part n k) := Δ[n+1]

def horn_start := ∐ (horn_f n k)
def excluded_end := ∐ (excluded_f n k)

def morph_horn_1 : horn_start n k ⟶ excluded_end n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.j.succ, idx.h₃⟩))

def morph_horn_2 : horn_start n k ⟶ excluded_end n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ (idx.j))
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.i.cast_succ, idx.h₂⟩))

def horn_morphism_i : excluded_part n k → (Δ[n+1] ⟶ Λ[n+2, k])
  := λ idx, yoneda_equiv.inv_fun ⟨simplex_category.δ idx.i, by {
    cases idx with i h₀,
    intro h,
    dsimp [simplex_category.δ, simplex_category.hom.mk] at h,
    simp [set.union_singleton, sSet.as_order_hom] at h,
    simp_rw [set.ext_iff] at h,
    specialize h i,
    have h' := h.mpr (set.mem_univ i),
    simp at h',
    cases h',
    contradiction,
    cases h',
    exact fin.succ_above_ne _ _ h'_h,
  }⟩

lemma horn_morphism_i_incl (idx : excluded_part n k) :
  horn_morphism_i n k idx ≫ sSet.horn_inclusion (n + 2) k = yoneda.map (simplex_category.δ idx.i)
  := rfl

def horn_morphism : excluded_end n k ⟶ Λ[n + 2, k] :=
  limits.sigma.desc (horn_morphism_i n k)

lemma horn_coeq : morph_horn_1 n k ≫ horn_morphism n k = morph_horn_2 n k ≫ horn_morphism n k :=
begin
  dsimp only [horn_morphism, horn_morphism_i, morph_horn_1, morph_horn_2],
  apply limits.colimit.hom_ext,
  simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
    equiv.inv_fun_as_coe, category.assoc],
  intro idx,
  rw [←equiv.apply_eq_iff_eq yoneda_equiv],
  rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality],
  rw [equiv.apply_symm_apply, equiv.apply_symm_apply],
  dsimp only [sSet.horn, simplex_category.hom.to_order_hom, coe_coe],
  simp only [quiver.hom.unop_op, subtype.coe_mk],
  cases idx with i j h₁ h₂ h₃,
  simp only [function.embedding.to_fun_eq_coe, rel_embedding.coe_fn_to_embedding],
  exact simplex_category.δ_comp_δ h₁,
end

def horn_fork : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k) 
  := limits.cofork.of_π (horn_morphism n k) (horn_coeq n k)

def matching_faces (X : sSet) (y : (excluded_part n k) -> X _[n+1]) :=
  ∀ idx : horn_part n k, X.δ idx.i (y ⟨idx.j.succ, idx.h₃⟩) = X.δ idx.j (y ⟨idx.i.cast_succ, idx.h₂⟩)

def horn_fork_faces (X : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k))
 : (excluded_part n k → X.X _[n + 1]) :=
  λ idx, yoneda_equiv (
    (limits.sigma.ι (excluded_f n k) idx : Δ[n+1] ⟶ excluded_end n k) ≫
    (X.π : excluded_end n k ⟶ X.X))

lemma horn_fork_matching_faces (X : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k))
  : matching_faces n k X.X (horn_fork_faces n k X) :=
begin
  intro idx,
  dsimp only [simplicial_object.δ, horn_fork_faces],
  simp_rw [yoneda_equiv_naturality],
  rw [equiv.apply_eq_iff_eq yoneda_equiv],
  have h := congr_arg (λ f, limits.sigma.ι (horn_f n k) idx ≫ f) X.condition,
  dsimp [morph_horn_1, morph_horn_2] at h,
  simp_rw [←category.assoc', limits.colimit.ι_desc] at h,
  simp only [limits.cofan.mk_ι_app, category.assoc] at h,
  exact h,
end 

def horn_hole {m n k} (f : [m] ⟶ [n + 1]) (h : set.range f.to_order_hom ∪ {k} ≠ set.univ)
  : ∃ i, i ≠ k ∧ i ∉ set.range f.to_order_hom :=
begin
  rw [set.ne_univ_iff_exists_not_mem] at h,
  cases h,
  use h_w,
  finish,
end

def horn_hole_index {m n k} (f : [m] ⟶ [n + 1]) (h : set.range f.to_order_hom ∪ {k} ≠ set.univ)
  := classical.some (horn_hole f h)

def horn_hole_neq_k {m n k} (f : [m] ⟶ [n + 1]) (h : set.range f.to_order_hom ∪ {k} ≠ set.univ)
  := (classical.some_spec (horn_hole f h)).1

def horn_hole_fun {m n k} (f : [m] ⟶ [n + 1]) (h : set.range f.to_order_hom ∪ {k} ≠ set.univ)
  := classical.some (hole_decomposition f (classical.some_spec (horn_hole f h)).2)

def horn_hole_prop {m n k} (f : [m] ⟶ [n + 1]) (h : set.range f.to_order_hom ∪ {k} ≠ set.univ)
  := classical.some_spec (hole_decomposition f (classical.some_spec (horn_hole f h)).2)

def horn_colim_obj {n m : ℕ}
  {k : fin (n + 3)}
  (s : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k))
  (f : [m] ⟶ [n + 2])
  (hf : set.range f.to_order_hom ∪ {k} ≠ set.univ) :
  s.X.obj (opposite.op [m]) :=
    s.X.map
      (horn_hole_fun f hf).op 
      (horn_fork_faces n k s ⟨horn_hole_index f hf, horn_hole_neq_k f hf⟩)

def horn_colim_obj_invariant {n m : ℕ}
  {i k : fin (n + 3)} (h : i ≠ k) (f : [m] ⟶ [n + 1])
  (s : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k))
  : horn_colim_obj s (f ≫ simplex_category.δ i) sorry =
    s.X.map f.op (horn_fork_faces n k s ⟨i, h⟩) :=
begin
  -- dsimp [horn_colim_obj],
  cases lt_trichotomy i (horn_hole_index (f ≫ simplex_category.δ i) sorry),
  case or.inl : h' {
    sorry
  },
  case or.inr : h' {
    cases h',
    case or.inl : h' {
        rw [horn_colim_obj],
        congr, swap, rw [←h'],
        have hf := horn_hole_prop (f ≫ simplex_category.δ i) sorry,
        simp [horn_hole_index] at h',
        rw [←h'] at hf,
        have hf' := δ_cancel f _ hf,
        
    },
    case or.inr : h' {

    },
  }
end
  

def horn_colim : limits.is_colimit (horn_fork n k) :=
begin
  sorry,
  -- apply limits.cofork.is_colimit.mk',
  -- intro s,
  -- dsimp [horn_fork],
  -- fconstructor,
  -- focus {
  --   refine nat_trans.mk _ _,
  --   focus {
  --     intros X f,
  --     cases f with f hf,
  --     let m := X.unop.len,
  --     have hX : X = opposite.op [m] := by simp only [simplex_category.mk_len, opposite.op_unop],
  --     clear_value m,
  --     subst hX,
  --     dsimp [sSet.standard_simplex] at f,
  --     -- let i := horn_hole f hf,
  --     -- let f' := hole_decomposition f (classical.some_spec i).2,
  --     exact horn_colim_obj s f hf,
  --   },
  --   focus {
  --     dsimp [auto_param],
  --     intros X Y f,
  --     let m := X.unop.len, let o := Y.unop.len,
  --     have hX : X = opposite.op [m] := by simp only [simplex_category.mk_len, opposite.op_unop],
  --     have hY : Y = opposite.op [o] := by simp only [simplex_category.mk_len, opposite.op_unop],
  --     clear_value m o,
  --     subst hX, subst hY,
  --     ext1,
  --     dsimp [sSet.horn, sSet.standard_simplex, excluded_end] at *,
  --     cases x,
  --     simp,
  --     sorry,
  --   },
  -- },
  -- split,
  -- focus {
  --   dsimp [horn_morphism],
  --   ext1,
  --   simp [horn_morphism_i],
  --   ext1, ext1,
  --   simp,
  -- },
  -- focus {
  --   intro ,
  --   dsimp [horn_fork],
  --   refine nat_trans.mk _ _,
  --   focus {
  --     intros X f,
  --     let m := X.unop.len,
  --     have hX : X = opposite.op [m] := by simp only [simplex_category.mk_len, opposite.op_unop],
  --     clear_value m,
  --     subst hX,
  --     cases f,
  --     apply yoneda_equiv.to_fun,
  --     dsimp [sSet.standard_simplex] at f_val,
  --     refine _ ≫ _,
  --     exact Δ[n + 1],
  --     apply yoneda_equiv.inv_fun,
  --     exact nonsurj_fun f_val (horn_nonsurj f_val f_property),
  --     refine _ ≫ s.π,
  --     exact limits.sigma.ι (excluded_f n k) ⟨nonsurj_index f_val (horn_nonsurj f_val f_property)⟩,
  --   },
  -- },
end
