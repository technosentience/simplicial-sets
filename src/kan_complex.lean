import algebraic_topology.simplex_category
import algebraic_topology.simplicial_set
import algebraic_topology.simplicial_object
import category_theory.arrow
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.products

open category_theory

noncomputable theory

universes u v

open_locale simplicial

def boundary_1 (n : ℕ) := -- n + 2
 @limits.sigma_obj _ _ sSet.large_category (λ idx : (Σ (i j : fin (n + 1)), plift (i < j)), Δ[n])

def boundary_2 (n : ℕ) :=
 @limits.sigma_obj _ _ sSet.large_category (λ idx : fin (n + 1), Δ[n + 1])

def morph1 (n : ℕ) :=
  @limits.sigma.desc _ _ sSet.large_category (λ idx : (Σ (i j : fin (n + 1)), plift (i < j)), Δ[n]) _
  (boundary_2 n) (λ idx, yoneda.map (simplex_category.δ idx.1) ≫ limits.sigma.ι _ idx.2.1)
  
def morph2 (n : ℕ) :=
  @limits.sigma.desc _ _ sSet.large_category (λ idx : (Σ j : fin (n + 1), fin j), Δ[n]) _
  (boundary_2 n) (λ idx, sigma.cases_on idx (λ j i, yoneda.map (simplex_category.δ i) ≫ limits.sigma.ι _ j))

#check morph1 0

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