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
import alt_horn

open category_theory

noncomputable theory

open_locale simplicial

universe u

variable n : ℕ
variable k : fin (n + 3)

def horn_has_filler {X : sSet} (f : Λ[n+2, k] ⟶ X) := 
  ∃ f' : Δ[n+2] ⟶ X, sSet.horn_inclusion (n + 2) k ≫ f' = f

def kan_complex (X : sSet) := ∀ (n k), ∀ f : Λ[n+2, k] ⟶ X, horn_has_filler n k f

def extension_condition (X : sSet) := ∀ (n k), ∀ y : (excluded_part n k) -> X _[n+1],
  (matching_faces n k X y) -> ∃ y' : X _[n+2], ∀ idx : excluded_part n k, X.δ idx.i y' = y idx

lemma kan_complex_impl_extension_condition (X : sSet) : kan_complex X -> extension_condition X :=
begin
  simp [kan_complex, extension_condition, matching_faces, horn_has_filler],
  intros kan n k y faces,
  set yₘ : excluded_end n k ⟶ X := limits.sigma.desc (λ idx, yoneda_equiv.inv_fun (y idx)),
  set y' : limits.cofork (morph_horn_1 n k) (morph_horn_2 n k) := limits.cofork.of_π yₘ (by {
    rewrite [morph_horn_1, morph_horn_2],
    apply limits.colimit.hom_ext,
    simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
      equiv.inv_fun_as_coe, category.assoc],
    intro idx,
    rw [←equiv.apply_eq_iff_eq yoneda_equiv],
    rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality],
    rw [equiv.apply_symm_apply, equiv.apply_symm_apply],
    exact faces idx,
  }),
  set f := (horn_colim n k).desc y',
  specialize kan n k f,
  cases kan,
  use (yoneda_equiv kan_w),
  intro idx,
  dsimp only [simplicial_object.δ],
  rw [yoneda_equiv_naturality],
  rw [equiv.apply_eq_iff_eq_symm_apply yoneda_equiv],

  have h' : (horn_morphism_i n k idx ≫ sSet.horn_inclusion (n + 2) k) ≫ kan_w = horn_morphism_i n k idx ≫ f
    := by simp [kan_h],
  simp [horn_morphism_i_incl, f] at h',
  
  have h'' := (horn_colim n k).fac y' limits.walking_parallel_pair.one,
  dsimp [horn_fork, limits.cofork.π_of_π] at h'',
  
  have h''' : ((limits.sigma.ι (excluded_f n k) idx) ≫ horn_morphism n k) ≫ (horn_colim n k).desc y'
    = (limits.sigma.ι (excluded_f n k) idx) ≫ yₘ := by simp [h''],
  simp [horn_morphism, limits.colimit.ι_desc] at h''',

  rwa [←h'''],
end

lemma extension_condition_impl_kan_complex (X : sSet) : extension_condition X -> kan_complex X :=
begin
  simp [kan_complex, extension_condition, matching_faces, horn_has_filler],
  intros face n k f,

  set y : excluded_part n k → X.obj (opposite.op [n + 1]) :=
    λ idx, yoneda_equiv (horn_morphism_i n k idx ≫ f),
  specialize face n k y,
  specialize face (by {
    intro idx,
    have h : limits.sigma.ι (horn_f n k) idx ≫ (morph_horn_1 n k ≫ horn_morphism n k) ≫ f = 
      limits.sigma.ι (horn_f n k) idx ≫ (morph_horn_2 n k ≫ horn_morphism n k) ≫ f := by rw [horn_coeq],
    dsimp [morph_horn_1, morph_horn_2, horn_morphism, horn_morphism_i] at h,
    simp at h,
    rw [←equiv.apply_eq_iff_eq yoneda_equiv] at h,
    rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality] at h,
    dsimp [simplicial_object.δ, y],
    simp [yoneda_equiv] at h,
    exact h,
  }),

  cases face,
  use yoneda_equiv.inv_fun face_w,
  
  dsimp only [y] at face_h,
  apply limits.cofork.is_colimit.hom_ext (horn_colim n k),
  dsimp [horn_fork],
  dsimp only [horn_morphism],
  
  apply limits.colimit.hom_ext,
  simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
    equiv.inv_fun_as_coe, category.assoc],
  intro idx,
  specialize face_h idx,
  rw [←category.assoc, horn_morphism_i_incl n k idx, ←equiv.apply_eq_iff_eq yoneda_equiv],
  rw [←yoneda_equiv_naturality, equiv.apply_symm_apply],
  exact face_h,
end

lemma kan_complex_iff_extension_conditions {X : sSet} : kan_complex X ↔ extension_condition X
  := ⟨kan_complex_impl_extension_condition X, extension_condition_impl_kan_complex X⟩
