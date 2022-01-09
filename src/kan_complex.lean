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

structure {x} boundary_part : Type x :=
  mk :: (i j : fin (n + 2)) (h : i ≤ j)

structure {x} end_part : Type x :=
  mk :: (i : fin (n + 3))

structure {x} horn_part : Type x :=
  mk :: (i j : fin (n + 2)) (h₁ : i ≤ j) (h₂ : i.cast_succ ≠ k) (h₃ : j.succ ≠ k)

structure {x} excluded_part : Type x :=
  mk :: (i : fin (n + 3)) (h : i ≠ k)

def boundary_f (p : boundary_part n) : sSet.{u} := Δ[n]
def simplex_f (p : end_part n) : sSet.{u} := Δ[n+1]

def horn_f (p : horn_part n k) : sSet.{u} := Δ[n]
def excluded_f (p : excluded_part n k) : sSet.{u} := Δ[n+1]

def boundary_start : sSet.{u} := ∐ (boundary_f n)
def horn_start : sSet.{u} := ∐ (horn_f n k)

def simplex_end : sSet.{u} := ∐ (simplex_f n)
def excluded_end : sSet.{u} := ∐ (excluded_f n k)

def morph_boundary_1 : boundary_start.{u} n ⟶ simplex_end.{u} n :=
  limits.sigma.desc
    (λ idx : boundary_part n, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.j.succ⟩))
  
def morph_boundary_2 : boundary_start.{u} n ⟶ simplex_end.{u} n :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.j)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.i.cast_succ⟩))

def boundary : sSet.{u} := limits.coequalizer (morph_boundary_1 n) (morph_boundary_2 n)

def morph_horn_1 : horn_start.{u} n k ⟶ excluded_end.{u} n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.j.succ, idx.h₃⟩))

def morph_horn_2 : horn_start.{u} n k ⟶ excluded_end.{u} n k :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ (idx.j))
      ≫ (limits.sigma.ι (excluded_f n k) ⟨idx.i.cast_succ, idx.h₂⟩))

def horn : sSet.{u} := limits.coequalizer (morph_horn_1 n k) (morph_horn_2 n k)

def boundary_morphism : simplex_end.{u} n ⟶ (∂Δ[n + 2] : sSet.{u}) :=
  limits.sigma.desc (λ b, yoneda_equiv.inv_fun ⟨simplex_category.δ b.i, by {
    simp only [not_exists, not_forall, coe_coe],
    use b.i,
    intros x,
    exact fin.succ_above_ne _ _,
  }⟩)

lemma boundary_coeq : morph_boundary_1.{u} n ≫ boundary_morphism.{u} n = morph_boundary_2.{u} n ≫ boundary_morphism.{u} n :=
begin
  rewrite [boundary_morphism, morph_boundary_1, morph_boundary_2],
  apply limits.colimit.hom_ext,
  simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
    equiv.inv_fun_as_coe, category.assoc],
  intro idx,
  rw [←equiv.apply_eq_iff_eq yoneda_equiv],
  rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality],
  rw [equiv.apply_symm_apply, equiv.apply_symm_apply],
  dsimp only [sSet.boundary, simplex_category.hom.to_preorder_hom, coe_coe],
  simp only [quiver.hom.unop_op, subtype.coe_mk],
  cases idx with i j h,
  simp only [function.embedding.to_fun_eq_coe, rel_embedding.coe_fn_to_embedding],
  exact simplex_category.δ_comp_δ h,
end

def boundary_fork := limits.cofork.of_π (boundary_morphism.{u} n) (boundary_coeq.{u} n)

def boundary_colim : limits.is_colimit (boundary_fork.{u} n) := sorry

def horn_morphism_i : excluded_part.{u} n k → ((Δ[n+1] : sSet.{u}) ⟶ (Λ[n+2, k] : sSet.{u}))
  := λ idx, yoneda_equiv.inv_fun ⟨simplex_category.δ idx.i, by {
    intro h,
    dsimp [simplex_category.δ, simplex_category.hom.mk] at *,
    simp only [set.union_singleton] at *,
    admit,
  }⟩

lemma horn_morphism_i_incl (idx : excluded_part.{u} n k) :
  horn_morphism_i n k idx ≫ sSet.horn_inclusion (n + 2) k = yoneda.map (simplex_category.δ idx.i) := sorry

def horn_morphism : excluded_end.{u} n k ⟶ (Λ[n + 2, k] : sSet.{u}) :=
  limits.sigma.desc (horn_morphism_i.{u} n k)

lemma horn_coeq : morph_horn_1.{u} n k ≫ horn_morphism.{u} n k = morph_horn_2.{u} n k ≫ horn_morphism n k :=
begin
  dsimp only [horn_morphism, horn_morphism_i, morph_horn_1, morph_horn_2],
  apply limits.colimit.hom_ext,
  simp only [limits.cofan.mk_ι_app, limits.colimit.ι_desc, limits.colimit.ι_desc_assoc, coe_coe,
    equiv.inv_fun_as_coe, category.assoc],
  intro idx,
  rw [←equiv.apply_eq_iff_eq yoneda_equiv],
  rw [←yoneda_equiv_naturality, ←yoneda_equiv_naturality],
  rw [equiv.apply_symm_apply, equiv.apply_symm_apply],
  dsimp only [sSet.horn, simplex_category.hom.to_preorder_hom, coe_coe],
  simp only [quiver.hom.unop_op, subtype.coe_mk],
  cases idx with i j h₁ h₂ h₃,
  simp only [function.embedding.to_fun_eq_coe, rel_embedding.coe_fn_to_embedding],
  exact simplex_category.δ_comp_δ h₁,
end

def horn_fork : limits.cofork (morph_horn_1.{u} n k) (morph_horn_2.{u} n k) 
  := limits.cofork.of_π (horn_morphism n k) (horn_coeq n k)

def horn_colim : limits.is_colimit (horn_fork.{u} n k) := sorry

def horn_has_filler {X : sSet.{u}} (f : Λ[n+2, k] ⟶ X) := 
  ∃ f' : Δ[n+2] ⟶ X, sSet.horn_inclusion (n + 2) k ≫ f' = f

def is_kan_complex (X : sSet.{u}) := ∀ {n k}, ∀ f : Λ[n+2, k] ⟶ X, horn_has_filler n k f


def connected_horn (X : sSet.{u}) (y : fin (n + 3) -> X _[n+1]) :=
  ∀ idx : horn_part.{u} n k, X.δ idx.i (y idx.j.succ) = X.δ idx.j (y idx.i.cast_succ)

def has_matching_faces (X : sSet.{u}) := ∀ {n k}, ∀ y : fin (n + 3) -> X _[n+1],
  (connected_horn.{u} n k X y) -> ∃ y' : X _[n+2], ∀ {i}, i ≠ k -> X.δ i y' = y i

lemma kan_complex_impl_matching_face (X : sSet.{u}) : is_kan_complex X -> has_matching_faces X :=
begin
  simp [is_kan_complex, has_matching_faces, connected_horn, horn_has_filler],
  intros kan n k y conn,
  set yₘ : excluded_end n k ⟶ X := limits.sigma.desc (λ idx, yoneda_equiv.inv_fun (y idx.i)),
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
  specialize kan f,
  cases kan,
  use (yoneda_equiv kan_w),
  intros i h,
  dsimp only [simplicial_object.δ],
  rw [yoneda_equiv_naturality],
  rw [equiv.apply_eq_iff_eq_symm_apply yoneda_equiv],

  have h' : (horn_morphism_i n k ⟨i, h⟩ ≫ sSet.horn_inclusion (n + 2) k) ≫ kan_w = horn_morphism_i n k ⟨i, h⟩ ≫ f
    := by simp [kan_h],
  simp [horn_morphism_i_incl, f] at h',
  
  have h'' := (horn_colim n k).fac y' limits.walking_parallel_pair.one,
  rw [←limits.cofork.π_eq_app_one] at h'',
  dsimp [horn_fork, limits.cofork.π_of_π] at h'',
  
  have h''' : ((limits.sigma.ι (excluded_f.{u} n k) ⟨i, h⟩) ≫ horn_morphism n k) ≫ (horn_colim n k).desc y'
    = (limits.sigma.ι (excluded_f.{u} n k) ⟨i, h⟩) ≫ yₘ := by simp [h''],
  simp [horn_morphism, limits.colimit.ι_desc] at h''',

  rwa [←h'''],
end

lemma matching_face_impl_kan_complex (X : sSet) : has_matching_faces X -> is_kan_complex X :=
begin
  simp [is_kan_complex, has_matching_faces, connected_horn, horn_has_filler],
  intros face n k f,
  fconstructor,
  apply yoneda_equiv.inv_fun, 
  admit,
  admit,
end