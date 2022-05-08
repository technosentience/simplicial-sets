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

open category_theory

noncomputable theory

open_locale simplicial

universes u v

variable n : ℕ
variable k : fin (n + 3)

structure boundary_part :=
  mk :: (i j : fin (n + 2)) (h : i ≤ j)

structure end_part :=
  mk :: (i : fin (n + 3))

structure horn_part :=
  mk :: (i j : fin (n + 2)) (h₁ : i ≤ j) (h₂ : i.cast_succ ≠ k) (h₃ : j.succ ≠ k)

structure excluded_part  :=
  mk :: (i : fin (n + 3)) (h : i ≠ k)

def boundary_f (p : boundary_part n) := Δ[n]
def simplex_f (p : end_part n) := Δ[n+1]

def horn_f (p : horn_part n k) := Δ[n]
def excluded_f (p : excluded_part n k) := Δ[n+1]

def boundary_start := ∐ (boundary_f n)
def horn_start := ∐ (horn_f n k)

def simplex_end := ∐ (simplex_f n)
def excluded_end := ∐ (excluded_f n k)

def morph_boundary_1 : boundary_start n ⟶ simplex_end n :=
  limits.sigma.desc
    (λ idx : boundary_part n, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.j.succ⟩))
  
def morph_boundary_2 : boundary_start n ⟶ simplex_end n :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.j)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.i.cast_succ⟩))

def boundary := limits.coequalizer (morph_boundary_1 n) (morph_boundary_2 n)

def morph_horn_1 : horn_start n k ⟶ excluded_end n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.j.succ, idx.h₃⟩))

def morph_horn_2 : horn_start n k ⟶ excluded_end n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ (idx.j))
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.i.cast_succ, idx.h₂⟩))

def horn := limits.coequalizer (morph_horn_1 n k) (morph_horn_2 n k)

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

def boundary_colim : limits.is_colimit (boundary_fork n) := sorry

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

def horn_colim : limits.is_colimit (horn_fork n k) := sorry

def horn_has_filler {X : sSet} (f : Λ[n+2, k] ⟶ X) := 
  ∃ f' : Δ[n+2] ⟶ X, sSet.horn_inclusion (n + 2) k ≫ f' = f

def is_kan_complex (X : sSet) := ∀ (n k), ∀ f : Λ[n+2, k] ⟶ X, horn_has_filler n k f


def connected_horn (X : sSet) (y : (excluded_part n k) -> X _[n+1]) :=
  ∀ idx : horn_part n k, X.δ idx.i (y ⟨idx.j.succ, idx.h₃⟩) = X.δ idx.j (y ⟨idx.i.cast_succ, idx.h₂⟩)

def has_matching_faces (X : sSet) := ∀ (n k), ∀ y : (excluded_part n k) -> X _[n+1],
  (connected_horn n k X y) -> ∃ y' : X _[n+2], ∀ idx : excluded_part n k, X.δ idx.i y' = y idx

lemma kan_complex_impl_matching_face (X : sSet) : is_kan_complex X -> has_matching_faces X :=
begin
  simp [is_kan_complex, has_matching_faces, connected_horn, horn_has_filler],
  intros kan n k y conn,
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
    exact conn idx,
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

lemma matching_face_impl_kan_complex (X : sSet) : has_matching_faces X -> is_kan_complex X :=
begin
  simp [is_kan_complex, has_matching_faces, connected_horn, horn_has_filler],
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

lemma kan_complex_iff_matching_faces {X : sSet} : is_kan_complex X ↔ has_matching_faces X
  := ⟨kan_complex_impl_matching_face X, matching_face_impl_kan_complex X⟩
