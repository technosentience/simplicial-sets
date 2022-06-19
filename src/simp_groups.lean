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

lemma sset_comp (X : sGrp) {i j k} (f : X _[i] ⟶ X _[j])
  (g : X _[j] ⟶ X _[k]) (x : X _[i]) : g (f x) = (f ≫ g) x := rfl

def u
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
  (r : fin (n + 3)) (h : r ≤ k) : G _[n + 2] :=
  fin.induction (λ h, 1) (λ r' ih h,
    have h' : r'.cast_succ < k := fin.cast_succ_lt_iff_succ_le.mpr h,
    let u' := ih (le_of_lt h') in
    u' * G.σ r' (G.δ r'.cast_succ (u' ⁻¹) * y ⟨r'.cast_succ, ne_of_lt h'⟩ ) ) r h

lemma du
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
(r i: fin (n + 3)) (h : r ≤ k) (hi : i < r) : G.δ i (u y faces r h) = y ⟨i, ne_of_lt (lt_of_lt_of_le hi h)⟩ :=
begin
  refine fin.induction _ _ r h i hi;
  clear hi i h r,
  focus {
    intros h i hi,
    cases hi,
  },
  intros r ih h i hi,
  have irlv : i ≠ k := ne_of_lt (lt_of_lt_of_le hi h),
  change G.δ i (u y faces r.succ h) = y {i := i, h := irlv},
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
    rw [simplicial_object.δ_comp_σ_self],
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
  have hc := faces ⟨j, r'.cast_succ, j_leq_r', j_neq_k, ne_of_lt r_lt_k⟩, simp only at hc,
  change simplicial_object.δ G j (y {i := r'.cast_succ.succ, h := _}) = simplicial_object.δ G r'.cast_succ (y {i := j.cast_succ, h := _}) at hc,
  simp_rw [fin.succ_cast_succ] at hc,
  rw hc,
  simp only [mul_left_inv, map_one],
end

def u'
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y) : G _[n + 2] := u y faces k (by refl)

def du'
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
  (i : fin (n + 3)) (h : i < k) : G.δ i (u' y faces) = y ⟨i, ne_of_lt h⟩ :=
begin
  dsimp [u'],
  apply du,
  assumption,
end

def w
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
  (r : fin (n + 3)) (h : r ≥ k) : G _[n + 2] :=
  fin.reverse_induction (λ _, u' y faces) (λ r' ih h,
    have h' : r'.succ > k := fin.le_cast_succ_iff.mp h, 
    let w' := ih (le_of_lt h') in
    w' * G.σ r' (G.δ r'.succ (w' ⁻¹) * y ⟨r'.succ, ne_of_gt h'⟩)) r h

def aux_dw 
  {r i : fin (n + 3)}
  (h : r ≥ k)
  (hi : i < k ∨ i > r) : i ≠ k :=
begin
  cases hi,
  exact ne_of_lt hi,
  exact ne_of_gt (gt_of_gt_of_ge hi h),
end


lemma dw
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
  (r i : fin (n + 3)) (h : r ≥ k) (hi : i < k ∨ i > r) :
  G.δ i (w y faces r h) = y ⟨i, aux_dw h hi⟩ :=
begin
  refine fin.reverse_induction _ _ r h i hi;
  clear' r h i hi,
  focus {
    intros h i ih,
    cases ih,
    dsimp [w],
    rw [fin.reverse_induction_last],
    apply du',
    exfalso,
    exact (not_le_of_gt ih (fin.le_last i)),
  },
  intros r ih h i hi,
  have irlv := aux_dw h hi,
  change G.δ i (w y faces (r.cast_succ) h) = y {i := i, h := irlv},
  by_cases hi' : r.succ = i,
  focus {
    subst hi',
    clear ih hi,
    simp_rw [w], rw [fin.reverse_induction_cast_succ],
    rw [←w],
    simp only [map_inv, map_mul],
    nth_rewrite 2 [sset_comp],
    nth_rewrite 0 [sset_comp],
    rw [simplicial_object.δ_comp_σ_succ],
    simp only [id_apply, mul_inv_cancel_left],
  },
  have hi'' : i < k ∨ i > r.succ := by {
    cases hi,
    left, assumption,
    right, refine ne.lt_of_le hi' (fin.cast_succ_lt_iff_succ_le.mp hi),
  },
  clear' hi hi', have hi := hi'', clear hi'',
  have r_succ_gt_k : r.succ > k := fin.le_cast_succ_iff.mp h, 
  specialize ih (le_of_lt r_succ_gt_k) i hi,
  simp_rw [w],
  rw [fin.reverse_induction_cast_succ],
  rw [←w],
  simp [ih],
  cases hi,
  case or.inl {
    set j := i.cast_pred,
    have hj : i = j.cast_succ := by {
      rw [fin.cast_succ_cast_pred],
      exact lt_of_lt_of_le hi (fin.le_last k),
    },
    simp_rw [hj] at irlv hi ih ⊢,
    set r' := r.pred (by {
      intro h0,
      have hk : 0 < k := lt_of_le_of_lt j.cast_succ.zero_le hi,
      rw h0 at h, simp at h,
      exact not_le_of_gt hk h,
    }),
    have hr : r = r'.succ := by rw [fin.succ_pred],
    simp_rw [hr] at h r_succ_gt_k ih ⊢,
    have j_leq_r' : j ≤ r'.cast_succ := by {
      rw [fin.cast_succ_lt_iff_succ_le] at hi,
      rw [←fin.succ_cast_succ] at h,
      have h' := le_trans hi h,
      rwa [fin.succ_le_succ_iff] at h',
    },
    have j_le_r'_succ : j ≤ r'.succ :=
      le_of_lt (lt_of_le_of_lt j_leq_r' fin.lt_succ),
    nth_rewrite 0 [sset_comp],
    nth_rewrite 1 [sset_comp],
    rw [simplicial_object.δ_comp_σ_of_le], swap, assumption,
    simp_rw [←sset_comp],
    nth_rewrite 1 [sset_comp],
    rw [simplicial_object.δ_comp_δ], swap, assumption,
    rw [←sset_comp],
    rw [ih],
    specialize faces ⟨j, r'.succ, j_le_r'_succ, irlv, ne_of_gt r_succ_gt_k⟩,
    simp only at faces,
    change G.δ j (y {i := r'.succ.succ, h := _}) =
      G.δ r'.succ (y {i := j.cast_succ, h := _}) at faces,
    rw [←faces_1],
    simp only [mul_left_inv],
  },
  case or.inr {
    set j := i.pred (by {
      intro h0, rw h0 at hi, cases hi,
    }),
    have hj : i = j.succ := by rw [fin.succ_pred],
    simp_rw [hj] at ih hi irlv ⊢,
    change r.succ < j.succ at hi,
    rw [fin.succ_lt_succ_iff] at hi_1,
    set r' := r.cast_pred,
    have hr : r = r'.cast_succ := by {
      rw [fin.cast_succ_cast_pred],
      exact lt_of_lt_of_le hi_1 (fin.le_last j),
    },
    simp_rw [hr] at h r_succ_gt_k ih hi_1 ⊢,
    have hi' : r'.succ ≤ j := fin.cast_succ_lt_iff_succ_le.mp hi_1,
    rw [fin.succ_cast_succ] at r_succ_gt_k,
    nth_rewrite 0 [sset_comp],
    nth_rewrite 1 [sset_comp],
    rw [simplicial_object.δ_comp_σ_of_gt], swap, assumption,
    simp_rw [←sset_comp],
    nth_rewrite 1 [sset_comp],
    simp_rw [fin.succ_cast_succ],
    rw [←simplicial_object.δ_comp_δ], swap, assumption,
    simp_rw [←fin.succ_cast_succ, ←sset_comp, ih],
    specialize faces ⟨r'.succ, j, hi', ne_of_gt r_succ_gt_k, irlv⟩,
    simp only at faces,
    change G.δ r'.succ (y {i := j.succ, h := _}) =
      G.δ j (y {i := r'.succ.cast_succ, h := _}) at faces,
    simp_rw [fin.succ_cast_succ, ←faces_1],
    simp only [mul_left_inv],
  },
end

def w'
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y) : G _[n + 2] := w y faces k (by fconstructor)

def dw'
  (y : excluded_part n k → G _[n + 1])
  (faces : matching_faces.{u} n k G y)
  (i : fin (n + 3)) (h : i ≠ k) : G.δ i (w' y faces) = y ⟨i, h⟩ :=
begin
  cases lt_trichotomy i k,
  apply dw, left, assumption,
  cases h_1, contradiction,
  apply dw, right, assumption,
end

def sGrp_Ext (G : sGrp.{0}) : extension_condition.{0} G :=
begin
  dsimp [extension_condition],
  intros n k y faces,
  use w' y faces,
  intro idx, cases idx,
  apply dw',
end

def sGrp_Kan (G : sGrp.{0}) : kan_complex G :=
  kan_complex_iff_extension_conditions.mpr (sGrp_Ext G)
