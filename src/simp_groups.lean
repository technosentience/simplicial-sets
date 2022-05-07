import algebraic_topology.simplicial_object
import algebra.category.Group.basic
import kan_complex

open category_theory

open_locale simplicial

universes u

variable n : ℕ
variable k : fin (n + 3)

@[derive [large_category]]
def sGrp : Type (u+1) := simplicial_object Group.{u}

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

def u (G : sGrp.{u}) {n : ℕ}
  {k : fin (n + 3)}
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y)
  (r : fin (n + 3)) (h : r < k) : G _[n + 2] :=
  fin.induction (λ h, G.σ 0 (y ⟨0, ne_of_lt h⟩))
  (λ r' ih h,
  let u' := ih (lt_trans fin.lt_succ h) in
  let a' := G.δ r'.succ (u' ⁻¹) in
  let b' := y ⟨r'.succ, ne_of_lt h⟩ in
  u' * G.σ r'.succ.cast_pred (a' * b') ) r h

lemma sset_comp (X : sGrp) {i j k} (f : X _[i] ⟶ X _[j])
  (g : X _[j] ⟶ X _[k]) (x : X _[i]) : g (f x) = (f ≫ g) x := rfl

lemma du (G : sGrp.{u}) {n : ℕ}
  {k : fin (n + 3)}
  (y : excluded_part n k → G _[n + 1])
  (conn : connected_horn.{u} n k G y)
(r i: fin (n + 3)) (h : r < k) (hi : i ≤ r) : G.δ i (u G y conn r h) = y ⟨i, ne_of_lt (gt_of_gt_of_ge h hi)⟩ :=
begin
  refine fin.induction _ _ r h i hi;
  clear hi i h r,
  focus {
    intros h i hi,
    cases i, cases hi,
    dsimp [u],
    rw [sset_comp],
    have h' := @simplicial_object.δ_comp_σ_self _ _ G (n + 1) 0,
    simp only [fin.cast_succ_zero] at h',
    rw h',
    refl
  },
  intros r ih h i hi,
  have h' := @simplicial_object.δ_comp_σ_self _ _ G (n + 1) r.succ.cast_pred,
  have h'' : fin.cast_succ r.succ.cast_pred = r.succ := by {
      rw [fin.cast_succ_cast_pred],
      exact gt_of_ge_of_gt (fin.le_last k) h,
  },
  rw h'' at h',
  have irlv : i ≠ k := ne_of_lt (gt_of_gt_of_ge h hi), 
  change G.δ i (u G y conn r.succ h) = y {i := i, h := irlv},
  by_cases hi' : i = r.succ,
  focus {
    subst hi',
    clear ih,
    dsimp [u],
    rw [induction_succ],
    rw [←u],
    swap, assumption,
    simp only [map_inv, map_mul],
    nth_rewrite 2 [sset_comp],
    nth_rewrite 0 [sset_comp],
    rw [h'],
    simp only [id_apply, mul_inv_cancel_left],
  },
  have hi'' : i < r.succ := ne.lt_of_le hi' hi,
  clear hi hi',
  have hi : i ≤ r.cast_succ := fin.le_cast_succ_iff.mpr hi'',
  have ihi := ih (lt_trans fin.lt_succ h) i hi,
  dsimp [u],
  rw [induction_succ],
  rw [←u], swap, assumption,
  simp [ihi],
  set j := i.cast_pred,
  have hj : j.cast_succ = i := by {
    rw [fin.cast_succ_cast_pred],
    exact gt_of_ge_of_gt (fin.le_last r.succ) hi'',
  },
  rw [←hj],
  have r_succ_leq_last : r.succ < fin.last (n + 2) := gt_of_ge_of_gt (fin.le_last k) h,
  have r_leq_last : r < fin.last (n + 1) := by {
    rw [←fin.succ_last, fin.succ_lt_succ_iff] at r_succ_leq_last,
    assumption,
  },
  have hr : r.succ.cast_pred = r.cast_pred.succ := by {
    rw [←fin.cast_succ_inj, ←fin.succ_cast_succ, fin.cast_succ_cast_pred, fin.cast_succ_cast_pred],
    swap,
    assumption,
    assumption,
  },
  rw [hr],
  nth_rewrite 0 [sset_comp],
  rw [simplicial_object.δ_comp_σ_of_le], swap,
  rw [fin.le_cast_succ_iff, ←fin.cast_succ_lt_cast_succ_iff],
  rw [hj, ←hr],
  rwa [fin.cast_succ_cast_pred],
  exact gt_of_ge_of_gt (fin.le_last k) h,
  rw [←sset_comp],
  nth_rewrite 1 [sset_comp],
  have j_leq_r : j ≤ r := by {
    rw le_iff_lt_or_eq,
    rw [←hj] at hi,
    cases lt_or_eq_of_le hi,
    left, rwa [←fin.cast_succ_lt_cast_succ_iff],
    right, rwa [←fin.cast_succ_inj],
  },
  rw [simplicial_object.δ_comp_δ], swap, assumption,
  rw [←sset_comp, hj, ihi],
  nth_rewrite 1 [sset_comp],
  simp_rw [←hj],
  rw [simplicial_object.δ_comp_σ_of_le], swap, rwa [fin.cast_succ_cast_pred], assumption,
  rw [←sset_comp, ←map_inv, ←map_mul],
  have j_neq_k : j.cast_succ ≠ k := by rwa hj,
  have hc := conn ⟨j, r, j_leq_r, j_neq_k, ne_of_lt h⟩, simp only at hc,
  change simplicial_object.δ G j (y {i := r.succ, h := _}) = simplicial_object.δ G r (y {i := j.cast_succ, h := _}) at hc,
  rw hc,
  simp only [mul_left_inv, map_one],
end

-- def sGrp_Ext (G : sGrp.{u}) : has_matching_faces.{u} G :=
-- begin
--   dsimp [has_matching_faces],
--   intros,
--   extract_goal,
-- end
