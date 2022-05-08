import algebraic_topology.simplicial_object
import algebra.category.Group.basic
import kan_complex

open category_theory

open_locale simplicial

universes u

variable {n : ℕ}
variable {k : fin (n + 3)}

@[derive [large_category]]
def sGrp : Type (u+1) := simplicial_object Group.{u}

variable {G : sGrp.{u}}

def to_sSet : sGrp.{u} ⥤ sSet.{u} := ((simplicial_object.whiskering _ _).obj (forget Group))

instance sGrp_to_sSet : has_coe sGrp sSet := ⟨to_sSet.obj⟩

@[simp]
lemma induction_zero
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) :
  @fin.induction n C h0 hs 0 = h0 := rfl

@[simp]
lemma induction_succ
  {C : fin (n + 1) → Sort*}
  (h0 : C 0)
  (hs : ∀ i : fin n, C i.cast_succ → C i.succ) (i : fin n) :
  @fin.induction n C h0 hs i.succ =
    hs i (@fin.induction n C h0 hs i.cast_succ) := by cases i; refl

@[simp]
lemma reverse_induction_cast_succ'
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) (i : fin n):
  @fin.reverse_induction n C h0 hs i.cast_succ =
    hs i (@fin.reverse_induction n C h0 hs i.succ) := by apply fin.reverse_induction_cast_succ

def u
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y)
  (r : fin (n + 3)) (h : r ≤ k) : G _[n + 2] :=
  fin.induction (λ h, 1) (λ r' ih h,
    have h' : r'.cast_succ < k := fin.cast_succ_lt_iff_succ_le.mpr h,
    let u' := ih (le_of_lt h') in
    u' * G.σ r' (G.δ r'.cast_succ (u' ⁻¹) * y ⟨r'.cast_succ, ne_of_lt h'⟩ ) ) r h

lemma sset_comp (X : sGrp) {i j k} (f : X _[i] ⟶ X _[j])
  (g : X _[j] ⟶ X _[k]) (x : X _[i]) : g (f x) = (f ≫ g) x := rfl

lemma du
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y)
(r i: fin (n + 3)) (h : r ≤ k) (hi : i < r) : G.δ i (u y conn r h) = y ⟨i, ne_of_lt (lt_of_lt_of_le hi h)⟩ :=
begin
  refine fin.induction _ _ r h i hi;
  clear hi i h r,
  focus {
    intros h i hi,
    cases hi,
  },
  intros r ih h i hi,
  have h' := @simplicial_object.δ_comp_σ_self _ _ G (n + 1) r,
  have irlv : i ≠ k := ne_of_lt (lt_of_lt_of_le hi h),
  change G.δ i (u y conn r.succ h) = y {i := i, h := irlv},
  by_cases hi' : i = r.cast_succ,
  focus {
    subst hi',
    clear ih,
    simp_rw [u],
    rw [induction_succ],
    rw [←u],
    swap, assumption,
    simp only [map_inv, map_mul],
    nth_rewrite 2 [sset_comp],
    nth_rewrite 0 [sset_comp],
    rw [h'],
    simp only [id_apply, mul_inv_cancel_left],
  },
  have hi'' : i < r.cast_succ := ne.lt_of_le hi' (fin.le_cast_succ_iff.mpr hi),
  clear hi hi',
  have hi := hi'', clear hi'',
  specialize ih (le_of_lt $ lt_of_lt_of_le fin.lt_succ h) i hi,
  simp_rw [u],
  rw [induction_succ],
  rw [←u], swap, assumption,
  simp only [ih, map_inv, map_mul, mul_right_eq_self],
  set j := i.cast_pred,
  have hj : i = j.cast_succ := by {
    rw [fin.cast_succ_cast_pred],
    exact lt_of_lt_of_le hi (fin.le_last r.cast_succ),
  },
  rw [hj],
  set r' := r.pred (by {
    intro h0,
    rw h0 at hi,
    cases hi,
  }),
  have hr : r = r'.succ := by rw [fin.succ_pred],
  simp_rw [hr],
  nth_rewrite 0 [sset_comp],
  rw [simplicial_object.δ_comp_σ_of_le], swap,
  rw [fin.le_cast_succ_iff, ←fin.cast_succ_lt_cast_succ_iff],
  rwa [←hj, ←hr],
  rw [←sset_comp],
  nth_rewrite 1 [sset_comp],
  simp_rw [←fin.succ_cast_succ],
  have j_leq_r' : j ≤ r'.cast_succ :=
    by rwa [fin.le_cast_succ_iff, ←hr, ←fin.cast_succ_lt_cast_succ_iff, ←hj],
  rw [simplicial_object.δ_comp_δ], swap, assumption,
  simp_rw [←sset_comp, ←hj, fin.succ_cast_succ, ←hr, ih],
  nth_rewrite 1 [sset_comp],
  simp_rw [hj, hr],
  rw [simplicial_object.δ_comp_σ_of_le], swap, assumption,
  rw [←sset_comp, ←map_inv, ←map_mul],
  have j_neq_k : j.cast_succ ≠ k := by rwa [←hj],
  have r_lt_k : r'.cast_succ.succ < k :=
    by rwa [fin.succ_cast_succ, ←hr, fin.cast_succ_lt_iff_succ_le],
  have hc := conn ⟨j, r'.cast_succ, j_leq_r', j_neq_k, ne_of_lt r_lt_k⟩, simp only at hc,
  change simplicial_object.δ G j (y {i := r'.cast_succ.succ, h := _}) = simplicial_object.δ G r'.cast_succ (y {i := j.cast_succ, h := _}) at hc,
  simp_rw [fin.succ_cast_succ] at hc,
  rw hc,
  simp only [mul_left_inv, map_one],
end

def u'
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y) : G _[n + 2] := u y conn k (by refl)

def du'
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y)
  (i : fin (n + 3)) (h : i < k) : G.δ i (u' y conn) = y ⟨i, ne_of_lt h⟩ :=
begin
  dsimp [u'],
  apply du,
  assumption,
end

-- def w
--   (y : excluded_part n k → G _[n + 1])
--   (conn : connected_horn.{u} n k G y)
--   (r : fin (n + 3)) (h : r > k) : G _[n + 2] :=
--     fin.reverse_induction (λ _, u' y conn) (λ r' ih h,
--       let w' := ih sorry in
--       let a' := G.δ r'.succ.cast_pred.cast_pred (w' ⁻¹) in
--       let b' := y ⟨r'.succ, sorry⟩ in
--       w' * G.σ r.cast_pred (a' * b')
--     ) r h

-- lemma dw
--   (y : excluded_part n k → G _[n + 1])
--   (conn : connected_horn.{u} n k G y)
--   (r i : fin (n + 3)) (h : r > k) (hi : i < k ∨ i ≥ r) :
--   G.δ i (w y conn r h) = y ⟨i, sorry⟩ :=
-- begin
--   refine fin.reverse_induction _ _ r h i hi;
--   clear' r h i hi,
--   focus {
--     intros h i ih,
--     cases ih, swap, sorry,
--     dsimp [w],
--     rw [fin.reverse_induction_last],
--     apply du', assumption,
--   },
--   intros r ih h i hi,
--   by_cases hi' : i = r.succ,
--   focus {
--     subst hi',
--     clear ih hi,
--     simp_rw [w], rw [reverse_induction_cast_succ'],
--     -- change G.δ r.succ (w y conn r.succ _) * G.σ r.cast_pred (G.δ r'.succ.cast_pred.cast_pred (w y conn r.succ))
--   }
-- end

-- def sGrp_Ext (G : sGrp.{u}) : has_matching_faces.{u} G :=
-- begin
--   dsimp [has_matching_faces],
--   intros,
--   extract_goal,
-- end
