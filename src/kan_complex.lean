import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import algebraic_topology.simplicial_object
import category_theory.arrow
import category_theory.discrete_category
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.limits.presheaf

open category_theory

noncomputable theory

open_locale simplicial

universes u v

abbreviation pi_obj' {β : Type u} (f : β → sSet.{u}) : sSet.{u} := limits.limit (discrete.functor f : discrete β ⥤ sSet)
abbreviation sigma_obj' {β : Type u} (f : β → sSet.{u}) : sSet.{u} := limits.colimit (discrete.functor f : discrete β ⥤ sSet)

notation `∏ ` f:20 := pi_obj' f
notation `∐ ` f:20 := sigma_obj' f

abbreviation pi.π {β : Type v} (f : β → sSet) (b : β) : ∏ f ⟶ f b :=
  limits.limit.π (discrete.functor f) b
abbreviation sigma.ι {β : Type v} (f : β → sSet) (b : β) : f b ⟶ ∐ f :=
  limits.colimit.ι (discrete.functor f) b

abbreviation pi.lift {β : Type v} (f : β → sSet) (P : sSet) (p : Π b, P ⟶ f b) : P ⟶ ∏ f :=
  limits.limit.lift _ (limits.fan.mk P p)
abbreviation sigma.desc {β : Type v} (f : β → sSet) (P : sSet) (p : Π b, f b ⟶ P) : ∐ f ⟶ P :=
  limits.colimit.desc _ (limits.cofan.mk P p)

section horns

variable n : ℕ
variable k : fin (n + 1)

structure {x} boundary_part : Type x :=
  mk :: (i j : fin (n + 2)) (h : i ≤ j)

structure {x} end_part : Type x :=
  mk :: (i : fin (n + 3))

-- structure horn_part :=
--   mk :: (i j : fin (n + 1)) (h₁ : i < j) (h₂ : i ≠ k) (h₃ : j ≠ k)

-- structure excluded_part :=
--   mk :: (i : fin (n + 1)) (h : i ≠ k)

def boundary_f (p : boundary_part n) := Δ[n]
def simplex_f (p : end_part.{u} n) : sSet.{u} := sSet.standard_simplex.obj.{u} (simplex_category.mk.{u} (n + 1))

-- def horn_f (p : horn_part n k) := Δ[n]
-- def excluded_f (p : excluded_part n k) := Δ[n + 1]

def simplex_end : sSet.{u} := sigma_obj'.{u} (simplex_f.{u} n)
-- def excluded_end := ∐ (excluded_f n k)

def morph_boundary_1 :=
  sigma.desc (boundary_f n) (simplex_end n)
    (λ idx, yoneda.map (simplex_category.δ idx.i)
      ≫ (sigma.ι (simplex_f n) ⟨idx.j.succ⟩))
  
def morph_boundary_2 :=
  sigma.desc (boundary_f n) (simplex_end n)
  (λ idx, yoneda.map (simplex_category.δ idx.j)
      ≫ (sigma.ι (simplex_f n) ⟨idx.i.cast_succ⟩))

def boundary := limits.coequalizer (morph_boundary_1 n) (morph_boundary_2 n)

-- def morph_horn_1 :=
--   sigma.desc (horn_f n k) (excluded_end n k)
--   (λ idx, yoneda.map (simplex_category.δ idx.i) ≫ (sigma.ι (excluded_f n k) ⟨idx.j, idx.h₃⟩))

-- def morph_horn_2 :=
--   sigma.desc (horn_f n k) (excluded_end n k)
--   (λ idx, yoneda.map (simplex_category.δ (idx.j - 1)) ≫ (sigma.ι (excluded_f n k) ⟨idx.i, idx.h₂⟩))

-- def horn := limits.coequalizer (morph_horn_1 n k) (morph_horn_2 n k)

set_option timeout 4000000000

def boundary_morphism : simplex_end n ⟶ ∂Δ[n + 2] :=
  sigma.desc _ _ (λ b, yoneda_equiv.inv_fun ⟨simplex_category.δ b.i, by {
    simp only [not_exists, not_forall, coe_coe],
    use b.i,
    intros x,
    exact fin.succ_above_ne _ _,
  }⟩)

def boundary_inv : ∂Δ[n + 2] ⟶ simplex_end n :=
  { app := λ m (a : {b : Δ[n + 2].obj m // _}), by {
      cases a, simp only [not_exists, not_forall] at a_property,
      set i := classical.some a_property,
      refine (sigma.ι _ _).app _ _,
      use i,
      dsimp [opposite] at m,
      dsimp [simplex_f, sSet.standard_simplex, opposite.unop] at *,
      have b := simplex_category.σ i.cast_pred,
      change [n + 2] ⟶ [n + 1] at b,
      exact @simplex_category.hom.comp m [n + 2] [n + 1] b a_val,
  } }

def boundary_coeq : morph_boundary_1 n ≫ boundary_morphism n = morph_boundary_2 n ≫ boundary_morphism n :=
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

def boundary_fork := limits.cofork.of_π (boundary_morphism n) (boundary_coeq n)

-- def boundary_colim : limits.is_colimit (boundary_fork n) :=
-- begin
--   refine limits.cofork.is_colimit.mk _ _ _ _,
--   focus {
--     intro s,
--     have p := s.π,
--     simp at p,
--     dsimp [boundary_fork],
--     refine _ ≫ p,
--     fconstructor,
--     intro X,
--     dsimp [sSet.boundary, simplex_end],
--   },
-- end

end horns

-- def horn_1 (n : ℕ) (k : fin (n + 1)) :=
--  @limits.sigma_obj _ _  sSet.large_category (λ idx : (Σ (i j : fin (n + 1))) )

def horn_has_filler {n i} {X : sSet} (f : Λ[n, i] ⟶ X) := 
  ∃ f' : Δ[n] ⟶ X, sSet.horn_inclusion n i ≫ f' = f

def is_kan_complex (X : sSet) := ∀ {n i}, ∀ f : Λ[n, i] ⟶ X, horn_has_filler f

def representing_map {n} (X : sSet) : (Δ[n] ⟶ X) ≃ X _[n] := yoneda_equiv

def connected_horn (X : sSet) : ∀ {n}, ∀ k : fin (n + 2), ∀ y : fin (n + 2) -> X _[n], Prop
| 0 k y := true
| (n + 1) k y := ∀ i j : fin (n + 2), i ≤ j -> i ≠ k -> j + 1 ≠ k -> X.δ i (y (j + 1)) = X.δ j (y i)

def has_matching_faces (X : sSet) := ∀ {n : ℕ}, ∀ k : fin (n + 2), ∀ y : fin (n + 2) -> X _[n], 
  connected_horn X k y -> ∃ y' : X _[n + 1], ∀ {i}, i ≠ k -> X.δ i y' = y i

-- lemma kan_complex_impl_matching_face (X : sSet) : is_kan_complex X -> has_matching_faces X :=
-- begin
--   simp [is_kan_complex, has_matching_faces],
--   intros kan n k y conn,
--   specialize kan n k,
--   sorry,
-- end

-- lemma matching_face_impl_kan_complex (X : sSet) : has_matching_faces X -> is_kan_complex X :=
-- begin
--   simp [is_kan_complex, has_matching_faces],
--   intros face n,
--   cases n,


-- end