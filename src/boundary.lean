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

universes u

variable n : ℕ
variable k : fin (n + 3)

open set
def test : set ℕ := { n // n.even }



structure {x} boundary_part : Type x :=
  mk :: (i j : fin (n + 2)) (h : i ≤ j)

structure {x} end_part : Type x :=
  mk :: (i : fin (n + 3))

def boundary_f (p : boundary_part n) : sSet.{u} := Δ[n]
def simplex_f (p : end_part n) : sSet.{u} := Δ[n+1]



def boundary_start : sSet.{u} := ∐ (boundary_f n)


def simplex_end : sSet.{u} := ∐ (simplex_f n)


def morph_boundary_1 : boundary_start.{u} n ⟶ simplex_end.{u} n :=
  limits.sigma.desc
    (λ idx : boundary_part n, yoneda.map (simplex_category.δ idx.i)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.j.succ⟩))
  
def morph_boundary_2 : boundary_start.{u} n ⟶ simplex_end.{u} n :=
  limits.sigma.desc
    (λ idx, yoneda.map (simplex_category.δ idx.j)
      ≫ (limits.sigma.ι (simplex_f n) ⟨idx.i.cast_succ⟩))

def boundary : sSet.{u} := limits.coequalizer (morph_boundary_1 n) (morph_boundary_2 n)


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






