import Mathlib.Topology.Order.Compact
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Finset

noncomputable def radius (n : ℕ) (r : ℝ) : ℝ :=
  (1 + 2 * n * (n + 1) * r) / (2 * (2 * n + 1))

noncomputable def load (n : ℕ) (r : ℝ) : ℝ := (2-r)/(2*n+1)

noncomputable def gapA (n : ℕ) (r : ℝ) : ℝ := (1+n*r)/(2*n+1)

noncomputable def gapB (n : ℕ) (r : ℝ) : ℝ := (1-(n+1)*r)/(2*n+1)

theorem denominator_pos (n : ℕ) : (0 : ℝ) < 2*n+1 := by positivity

theorem phase_lower (n : ℕ) (r : ℝ) (hn : 1 ≤ n)
    (hu : r ≤ 1/(2*(n:ℝ)^2)) : (n:ℝ)*r ≤ radius n r := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < 2*(n:ℝ)^2 := by positivity
  have hb := (le_div_iff₀ hp).mp hu
  apply (le_div_iff₀ (show (0:ℝ)<2*(2*n+1) by positivity)).mpr
  nlinarith

theorem phase_upper (n : ℕ) (r : ℝ)
    (hl : 1/(2*((n:ℝ)+1)^2) ≤ r) : radius n r ≤ ((n:ℝ)+1)*r := by
  have hp : (0:ℝ) < 2*((n:ℝ)+1)^2 := by positivity
  have hb := (div_le_iff₀ hp).mp hl
  apply (div_le_iff₀ (show (0:ℝ)<2*(2*n+1) by positivity)).mpr
  nlinarith

theorem sum_ramps (n : ℕ) (R r : ℝ) :
    2*R + 4 * (∑ j ∈ Finset.range n, (R - ((j:ℝ)+1)*r)) =
    2*(2*(n:ℝ)+1)*R - 2*n*(n+1)*r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

theorem critical_total (n : ℕ) (r : ℝ) :
    2 * radius n r + 4 * (∑ j ∈ Finset.range n, (radius n r - ((j:ℝ)+1)*r)) = 1 := by
  rw [sum_ramps]
  dsimp [radius]
  field_simp
  ring

theorem gap_identities (n : ℕ) (r : ℝ) :
    gapA n r + gapB n r = load n r ∧
    1 - (n:ℝ)*load n r = gapA n r ∧
    gapA n r = 2*radius n r - (n:ℝ)*r ∧
    gapB n r = 2*radius n r - ((n:ℝ)+1)*r := by
  dsimp [gapA, gapB, load, radius]
  have hd : (2*(n:ℝ)+1) ≠ 0 := ne_of_gt (denominator_pos n)
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

theorem two_intervals_cover (c d u v x : ℝ)
    (_hu : 0 ≤ u) (_hv : 0 ≤ v) (hg : d-c ≤ u+v)
    (hx : c ≤ x ∧ x ≤ d) : |x-c| ≤ u ∨ |x-d| ≤ v := by
  by_cases h : x ≤ c+u
  · left; rw [abs_of_nonneg (by linarith)]; linarith
  · right; rw [abs_of_nonpos (by linarith)]; linarith

theorem finite_touching_cover (N : ℕ) (c ρ : ℕ → ℝ)
    (hn : ∀ i ≤ N, 0 ≤ ρ i)
    (hg : ∀ i < N, c (i+1)-c i ≤ ρ i+ρ (i+1))
    (x : ℝ) (hx : c 0 ≤ x ∧ x ≤ c N) :
    ∃ i ≤ N, |x-c i| ≤ ρ i := by
  induction N with
  | zero =>
    refine ⟨0, le_refl _, ?_⟩
    have he : x=c 0 := by linarith
    simpa [he] using hn 0 (le_refl _)
  | succ N ih =>
    by_cases h : x ≤ c N
    · obtain ⟨i, hi, hc⟩ := ih (fun i hi => hn i (by omega))
        (fun i hi => hg i (by omega)) ⟨hx.1,h⟩
      exact ⟨i, by omega, hc⟩
    · rcases two_intervals_cover (c N) (c (N+1)) (ρ N) (ρ (N+1)) x
        (hn N (by omega)) (hn (N+1) (le_refl _)) (hg N (by omega))
        ⟨by linarith,hx.2⟩ with hN | hN
      · exact ⟨N, by omega, hN⟩
      · exact ⟨N+1, le_refl _, hN⟩

noncomputable def centers (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then (k/2 : ℕ) * load n r else (k/2 : ℕ) * load n r + gapA n r

noncomputable def radii (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then radius n r - (k/2 : ℕ) * r
  else radius n r - ((n:ℝ) - (k/2 : ℕ))*r

theorem center_even (n j : ℕ) (r : ℝ) : centers n r (2*j) = (j:ℝ)*load n r := by
  simp [centers]

theorem center_odd (n j : ℕ) (r : ℝ) : centers n r (2*j+1) = (j:ℝ)*load n r + gapA n r := by
  simp [centers, Nat.add_div]

theorem radius_even (n j : ℕ) (r : ℝ) : radii n r (2*j) = radius n r - (j:ℝ)*r := by
  simp [radii]

theorem radius_odd (n j : ℕ) (r : ℝ) : radii n r (2*j+1) = radius n r - ((n:ℝ)-(j:ℝ))*r := by
  simp [radii, Nat.add_div]

theorem parity_representation (k : ℕ) : (∃ j, k=2*j) ∨ (∃ j, k=2*j+1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · left; exact ⟨k/2, by omega⟩
  · right; exact ⟨k/2, by omega⟩

theorem radii_nonnegative (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hR : (n:ℝ)*r ≤ radius n r) (k : ℕ) (hk : k ≤ 2*n+1) :
    0 ≤ radii n r k := by
  rcases parity_representation k with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · rw [radius_even]
    have hj : j ≤ n := by omega
    have hjR : (j:ℝ) ≤ n := by exact_mod_cast hj
    nlinarith
  · rw [radius_odd]
    have hjR : (0:ℝ) ≤ j := by positivity
    nlinarith

theorem touching_gaps (n : ℕ) (r : ℝ) (k : ℕ) (hk : k < 2*n+1) :
    centers n r (k+1)-centers n r k = radii n r k+radii n r (k+1) := by
  obtain ⟨hab, ha, har, hbr⟩ := gap_identities n r
  rcases parity_representation k with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · rw [center_odd,center_even,radius_even,radius_odd]
    linarith
  · have he : 2*j+1+1=2*(j+1) := by omega
    rw [he,center_even,center_odd,radius_odd,radius_even]
    push_cast
    nlinarith

theorem optimal_interval_cover (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hu : r ≤ 1/(2*(n:ℝ)^2)) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∃ k ≤ 2*n+1, |x-centers n r k| ≤ radii n r k := by
  apply finite_touching_cover (2*n+1) (centers n r) (radii n r)
  · exact radii_nonnegative n r hr (phase_lower n r hn hu)
  · intro k hk
    exact le_of_eq (touching_gaps n r k hk)
  · have h0 : centers n r 0=0 := by simp [centers]
    have h1 : centers n r (2*n+1)=1 := by
      rw [center_odd]
      linarith [(gap_identities n r).2.1]
    simpa [h0,h1] using hx

theorem centers_are_orbit_points (n k : ℕ) (r : ℝ) (hk : k ≤ 2*n+1) :
    ∃ i m : ℤ, |i| ≤ (n:ℤ) ∧
      centers n r k = (i:ℝ)*load n r + (m:ℝ) ∧
      radii n r k = radius n r - |(i:ℝ)| *r := by
  rcases parity_representation k with ⟨j,rfl⟩ | ⟨j,rfl⟩
  · have hj : j ≤ n := by omega
    refine ⟨(j:ℤ),0,?_,?_,?_⟩
    · simpa using (show (j:ℤ) ≤ n by exact_mod_cast hj)
    · simp [center_even]
    · simp [radius_even]
  · have hj : j ≤ n := by omega
    have hjR : (j:ℝ) ≤ n := by exact_mod_cast hj
    have hjZ : (j:ℤ) ≤ n := by exact_mod_cast hj
    refine ⟨(j:ℤ)-(n:ℤ),1,?_,?_,?_⟩
    · rw [abs_of_nonpos (by omega)]
      omega
    · rw [center_odd]
      push_cast
      have ha := (gap_identities n r).2.1
      nlinarith
    · rw [radius_odd]
      push_cast
      rw [abs_of_nonpos (by linarith)]
      ring

theorem optimal_orbit_cover (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hu : r ≤ 1/(2*(n:ℝ)^2)) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    ∃ i m : ℤ, |i| ≤ (n:ℤ) ∧
      |(i:ℝ)| *r + |x-((i:ℝ)*load n r+(m:ℝ))| ≤ radius n r := by
  obtain ⟨k,hk,hc⟩ := optimal_interval_cover n r hn hr hu x hx
  obtain ⟨i,m,hi,he,hρ⟩ := centers_are_orbit_points n k r hk
  refine ⟨i,m,hi,?_⟩
  rw [he,hρ] at hc
  linarith

open MeasureTheory Metric

abbrev OrbitIndices (n : ℕ) := Option (Fin n ⊕ Fin n)

def orbitInteger (n : ℕ) : OrbitIndices n → ℤ
  | none => 0
  | some (.inl j) => (j.val:ℤ)+1
  | some (.inr j) => -((j.val:ℤ)+1)

theorem orbit_index_bound (n : ℕ) (i : OrbitIndices n) :
    |((orbitInteger n i):ℝ)| ≤ (n:ℝ) := by
  cases i with
  | none => simp [orbitInteger]
  | some i =>
    cases i with
    | inl j =>
      have h : (j.val:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
      simpa [orbitInteger, abs_of_nonneg (show (0:ℝ)≤j.val+1 by positivity)] using h
    | inr j =>
      have h : (j.val:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
      simp only [orbitInteger, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      exact h

theorem indexed_ramp_sum (n : ℕ) (r R : ℝ) :
    (∑ i : OrbitIndices n, 2*(R-|((orbitInteger n i):ℝ)| * r)) =
      2*R+4*(∑ j ∈ Finset.range n, (R-((j:ℝ)+1)*r)) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [orbitInteger, Int.cast_zero, abs_zero, zero_mul, sub_zero,
    Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg]
  have h : ∀ j : Fin n, |(j.val:ℝ)+1|=(j.val:ℝ)+1 := fun j => abs_of_nonneg (by positivity)
  simp_rw [h]
  rw [← Finset.mul_sum]
  have hf := Fin.sum_univ_eq_sum_range (fun j : ℕ => R-((j:ℝ)+1)*r) n
  rw [hf]
  ring

theorem circle_cover_length {ι : Type} [Fintype ι] (c : ι → UnitAddCircle) (a : ι → ℝ)
    (hc : ∀ x, ∃ i, dist x (c i) ≤ a i) :
    1 ≤ ∑ i, 2*max 0 (a i) := by
  have hsub : Set.univ ⊆ ⋃ i, closedBall (c i) (a i) := by
    intro x _
    obtain ⟨i,hi⟩ := hc x
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hmeasure : (1:ENNReal) ≤ ∑ i, ENNReal.ofReal (2*max 0 (a i)) := by
    calc
      1 = volume (Set.univ : Set UnitAddCircle) := UnitAddCircle.measure_univ.symm
      _ ≤ volume (⋃ i, closedBall (c i) (a i)) := measure_mono hsub
      _ ≤ ∑ i, volume (closedBall (c i) (a i)) := measure_iUnion_fintype_le volume _
      _ ≤ ∑ i, ENNReal.ofReal (2*max 0 (a i)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [AddCircle.volume_closedBall]
        apply ENNReal.ofReal_le_ofReal
        exact le_trans (min_le_right _ _) (by nlinarith [le_max_right (0:ℝ) (a i)])
  have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ 2*max 0 (a i) := by
    intro i _; positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hn] at hmeasure
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa [ENNReal.toReal_ofReal (Finset.sum_nonneg hn)] using ht

theorem phase_radius_positive (n : ℕ) (r : ℝ) (hr : 0 ≤ r) : 0 < radius n r := by
  unfold radius
  positivity

theorem no_subcritical_circle_cover (n : ℕ) (r R : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hu : r ≤ 1/(2*(n:ℝ)^2)) (hR : R < radius n r)
    (c : OrbitIndices n → UnitAddCircle) :
    ¬ (∀ x, ∃ i, dist x (c i) ≤ R-|((orbitInteger n i):ℝ)| * r) := by
  intro hc
  have hlen := circle_cover_length c (fun i => R-|((orbitInteger n i):ℝ)| * r) hc
  have hnonneg : ∀ i : OrbitIndices n, 0 ≤ radius n r - |((orbitInteger n i):ℝ)| * r := by
    intro i
    have hb := orbit_index_bound n i
    have hp := phase_lower n r hn hu
    nlinarith
  have hs : (∑ i : OrbitIndices n, 2*max 0 (R-|((orbitInteger n i):ℝ)| * r)) <
      ∑ i : OrbitIndices n, 2*(radius n r-|((orbitInteger n i):ℝ)| * r) := by
    apply Finset.sum_lt_sum
    · intro i _
      have hi := hnonneg i
      have hm : max 0 (R-|((orbitInteger n i):ℝ)| * r) ≤ radius n r-|((orbitInteger n i):ℝ)| * r :=
        max_le hi (by linarith)
      linarith
    · refine ⟨none,Finset.mem_univ _,?_⟩
      simp only [orbitInteger, Int.cast_zero, abs_zero, zero_mul, sub_zero]
      have hp := phase_radius_positive n r hr
      have hm : max 0 R < radius n r := max_lt hp hR
      linarith
  rw [indexed_ramp_sum, critical_total] at hs
  linarith

theorem orbit_index_surjective (n : ℕ) (k : ℤ) (hk : |k| ≤ (n:ℤ)) :
    ∃ i : OrbitIndices n, orbitInteger n i=k := by
  cases k with
  | ofNat m =>
    cases m with
    | zero => exact ⟨none,rfl⟩
    | succ j =>
      have hj : j < n := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hk
        rw [abs_of_nonneg (by positivity)] at hk
        omega
      refine ⟨some (.inl ⟨j,hj⟩),?_⟩
      simp [orbitInteger]
  | negSucc j =>
    have hj : j < n := by
      simp only [Int.negSucc_eq, abs_neg] at hk
      rw [abs_of_nonneg (by omega)] at hk
      omega
    refine ⟨some (.inr ⟨j,hj⟩),?_⟩
    simp [orbitInteger, Int.negSucc_eq]

def Covers (α : UnitAddCircle) (r R : ℝ) : Prop :=
  ∀ x : UnitAddCircle, ∃ k : ℤ, |(k:ℝ)| * r + dist x (k • α) ≤ R

theorem uniform_cover_radius_lower (n : ℕ) (r R : ℝ) (hn : 1 ≤ n)
    (hl : 1/(2*((n:ℝ)+1)^2) ≤ r) (hu : r ≤ 1/(2*(n:ℝ)^2))
    (α : UnitAddCircle) (hc : Covers α r R) : radius n r ≤ R := by
  by_contra h
  have hR : R < radius n r := lt_of_not_ge h
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hl
  apply no_subcritical_circle_cover n r R hn hr.le hu hR
    (fun i => orbitInteger n i • α)
  intro x
  obtain ⟨k,hk⟩ := hc x
  have hb : |(k:ℝ)| < (n:ℝ)+1 := by
    have hh := phase_upper n r hl
    have hd : (0:ℝ) ≤ dist x (k • α) := dist_nonneg
    nlinarith
  have hbZ : |k| < (n:ℤ)+1 := by exact_mod_cast hb
  obtain ⟨i,hi⟩ := orbit_index_surjective n k (by omega)
  refine ⟨i,?_⟩
  rw [hi]
  linarith

theorem quotient_distance_le (x y : ℝ) :
    dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ |x-y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem integer_coe_zero (m : ℤ) : ((m:ℝ):UnitAddCircle)=0 := by
  apply (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr
  exact ⟨m, by simp⟩

theorem optimal_circle_cover (n : ℕ) (r : ℝ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hu : r ≤ 1/(2*(n:ℝ)^2)) : Covers (load n r : UnitAddCircle) r (radius n r) := by
  intro x
  obtain ⟨y,hy,rfl⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨i,m,_,hi⟩ := optimal_orbit_cover n r hn hr hu y ⟨hy.1,hy.2.le⟩
  have hd := quotient_distance_le y ((i:ℝ)*load n r+(m:ℝ))
  have he : (((i:ℝ)*load n r+(m:ℝ) : ℝ):UnitAddCircle)=i • (load n r : UnitAddCircle) := by
    rw [AddCircle.coe_add, integer_coe_zero, add_zero]
    simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul (1:ℝ) (n:=i) (x:=load n r))
  rw [he] at hd
  exact ⟨i,by linarith⟩

theorem exact_optimal_design (n : ℕ) (r : ℝ) (hn : 1 ≤ n)
    (hl : 1/(2*((n:ℝ)+1)^2) ≤ r) (hu : r ≤ 1/(2*(n:ℝ)^2)) :
    Covers (load n r : UnitAddCircle) r (radius n r) ∧
    ∀ (α : UnitAddCircle) (R : ℝ), Covers α r R → radius n r ≤ R := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hl
  exact ⟨optimal_circle_cover n r hn hr.le hu,
    fun α R hc => uniform_cover_radius_lower n r R hn hl hu α hc⟩

#print axioms phase_lower
#print axioms phase_upper
#print axioms sum_ramps
#print axioms critical_total
#print axioms gap_identities
#print axioms two_intervals_cover
#print axioms finite_touching_cover
#print axioms optimal_interval_cover
#print axioms centers_are_orbit_points
#print axioms optimal_orbit_cover
#print axioms indexed_ramp_sum
#print axioms circle_cover_length
#print axioms no_subcritical_circle_cover
#print axioms uniform_cover_radius_lower
#print axioms optimal_circle_cover
#print axioms exact_optimal_design


namespace SPJMSAudit

theorem covers_half (α : UnitAddCircle) (r : ℝ) : Covers α r (1/2) := by
  intro x
  refine ⟨0, ?_⟩
  have h := AddCircle.norm_le_half_period (1:ℝ) (x:=x) (by norm_num)
  simpa only [Int.cast_zero, abs_zero, zero_mul, zero_zsmul, zero_add,
    dist_zero_right, abs_one] using h

theorem covers_noise_mono (α : UnitAddCircle) (r s R : ℝ)
    (hrs : s ≤ r) (h : Covers α r R) : Covers α s R := by
  intro x
  obtain ⟨k,hk⟩ := h x
  refine ⟨k,?_⟩
  nlinarith [abs_nonneg (k:ℝ)]

theorem saturated_optimal_design (α : UnitAddCircle) (r : ℝ) (hr : 1/2 ≤ r) :
    Covers α r (1/2) ∧ ∀ R : ℝ, Covers α r R → 1/2 ≤ R := by
  refine ⟨covers_half α r, ?_⟩
  intro R hc
  have hl := uniform_cover_radius_lower 1 (1/2) R (by norm_num)
    (by norm_num) (by norm_num) α (covers_noise_mono α r (1/2) R hr hc)
  norm_num [radius] at hl
  exact hl

theorem optimal_load_in_unit_interval (n : ℕ) (r : ℝ) (hn : 1 ≤ n)
    (hr : 0 ≤ r) (hu : r ≤ 1/(2*(n:ℝ)^2)) : 0 < load n r ∧ load n r < 1 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0:ℝ) < 2*(n:ℝ)^2 := by positivity
  have hb := (le_div_iff₀ hp).mp hu
  have hs : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hrhalf : r ≤ 1/2 := by nlinarith
  dsimp [load]
  constructor
  · exact div_pos (by linarith) (denominator_pos n)
  · apply (div_lt_one (denominator_pos n)).mpr
    linarith

theorem positive_noise_has_phase (r : ℝ) (hr : 0 < r) (hu : r ≤ 1/2) :
    ∃ n : ℕ, 1 ≤ n ∧ 1/(2*((n:ℝ)+1)^2) ≤ r ∧ r ≤ 1/(2*(n:ℝ)^2) := by
  have hex : ∃ n : ℕ, 1 < 2*((n:ℝ)+1)^2*r := by
    obtain ⟨N,hN⟩ := exists_nat_gt (1/r)
    have hNr : 1 < (N:ℝ)*r := (div_lt_iff₀ hr).mp hN
    have hsq : (N:ℝ) ≤ 2*((N:ℝ)+1)^2 := by nlinarith [sq_nonneg (N:ℝ)]
    have hm := mul_le_mul_of_nonneg_right hsq hr.le
    exact ⟨N, lt_of_lt_of_le hNr hm⟩
  let n := Nat.find hex
  have hnprop : 1 < 2*((n:ℝ)+1)^2*r := Nat.find_spec hex
  have hn : 1 ≤ n := by
    by_contra h
    have hz : n=0 := by omega
    rw [hz] at hnprop
    norm_num at hnprop
    linarith
  have hprev : ¬ 1 < 2*(((n-1:ℕ):ℝ)+1)^2*r := Nat.find_min hex (by omega)
  have hcast : ((n-1:ℕ):ℝ)+1=(n:ℝ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast] at hprev
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨n,hn,?_,?_⟩
  · apply (div_le_iff₀ (show (0:ℝ)<2*((n:ℝ)+1)^2 by positivity)).mpr
    nlinarith
  · apply (le_div_iff₀ (show (0:ℝ)<2*(n:ℝ)^2 by positivity)).mpr
    linarith

theorem phase_endpoint_agreement (n m : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnl : 1/(2*((n:ℝ)+1)^2) ≤ r) (hnu : r ≤ 1/(2*(n:ℝ)^2))
    (hml : 1/(2*((m:ℝ)+1)^2) ≤ r) (hmu : r ≤ 1/(2*(m:ℝ)^2)) :
    radius n r = radius m r := by
  obtain ⟨cn,ln⟩ := exact_optimal_design n r hn hnl hnu
  obtain ⟨cm,lm⟩ := exact_optimal_design m r hm hml hmu
  exact le_antisymm (ln _ _ cm) (lm _ _ cn)

end SPJMSAudit

#print axioms SPJMSAudit.covers_half
#print axioms SPJMSAudit.covers_noise_mono
#print axioms SPJMSAudit.saturated_optimal_design
#print axioms SPJMSAudit.optimal_load_in_unit_interval
#print axioms SPJMSAudit.positive_noise_has_phase
#print axioms SPJMSAudit.phase_endpoint_agreement

namespace SPJMSEnvelope

noncomputable def cone (L ε : ℝ) (a x : UnitAddCircle) (k : ℤ) : ℝ :=
  |(k : ℝ)| * ε + L * dist x (k • a)

noncomputable def envelope (L ε : ℝ) (a x : UnitAddCircle) : ℝ :=
  ⨅ k : ℤ, cone L ε a x k

theorem cone_nonnegative (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) (k : ℤ) : 0 ≤ cone L ε a x k := by
  exact add_nonneg (mul_nonneg (abs_nonneg _) hε) (mul_nonneg hL dist_nonneg)

theorem cone_bddBelow (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : BddBelow (Set.range (cone L ε a x)) := by
  exact ⟨0, by rintro z ⟨k,rfl⟩; exact cone_nonnegative L ε hL hε a x k⟩

theorem envelope_nonnegative (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : 0 ≤ envelope L ε a x := by
  exact le_ciInf (cone_nonnegative L ε hL hε a x)

theorem envelope_le_cone (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) (k : ℤ) : envelope L ε a x ≤ cone L ε a x k :=
  ciInf_le (cone_bddBelow L ε hL hε a x) k

theorem envelope_le_zero_cone (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : envelope L ε a x ≤ L * dist x 0 := by
  simpa [cone] using envelope_le_cone L ε hL hε a x 0

theorem envelope_le_half (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : envelope L ε a x ≤ L / 2 := by
  have hn : dist x 0 ≤ (1 : ℝ)/2 := by
    simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := x) (by norm_num)
  calc
    envelope L ε a x ≤ L * dist x 0 := envelope_le_zero_cone L ε hL hε a x
    _ ≤ L * (1/2) := mul_le_mul_of_nonneg_left hn hL
    _ = L/2 := by ring

theorem envelope_zero (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a : UnitAddCircle) : envelope L ε a 0 = 0 := by
  apply le_antisymm
  · simpa using envelope_le_zero_cone L ε hL hε a 0
  · exact envelope_nonnegative L ε hL hε a 0

theorem envelope_le_add_distance (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x y : UnitAddCircle) : envelope L ε a x ≤ envelope L ε a y + L * dist x y := by
  have hh : envelope L ε a x - L * dist x y ≤ envelope L ε a y := by
    apply le_ciInf
    intro k
    have hk := envelope_le_cone L ε hL hε a x k
    have ht := mul_le_mul_of_nonneg_left (dist_triangle x y (k • a)) hL
    dsimp [cone] at hk ⊢
    linarith
  linarith

theorem envelope_lipschitz (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x y : UnitAddCircle) : |envelope L ε a x - envelope L ε a y| ≤ L * dist x y := by
  apply abs_le.mpr
  have hx := envelope_le_add_distance L ε hL hε a x y
  have hy := envelope_le_add_distance L ε hL hε a y x
  rw [dist_comm y x] at hy
  constructor <;> linarith

theorem envelope_continuous (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a : UnitAddCircle) : Continuous (envelope L ε a) := by
  exact (LipschitzWith.of_le_add_mul ⟨L,hL⟩ (envelope_le_add_distance L ε hL hε a)).continuous

theorem cone_shift_upper (L ε : ℝ) (hε : 0 ≤ ε) (a x : UnitAddCircle) (k : ℤ) :
    cone L ε a (x+a) (k+1) ≤ cone L ε a x k + ε := by
  have hd : dist (x+a) ((k+1) • a) = dist x (k • a) := by
    simp only [add_zsmul, one_zsmul]
    exact dist_add_right _ _ _
  have hk : |((k+1 : ℤ) : ℝ)| ≤ |(k : ℝ)| + 1 := by
    push_cast
    simpa using abs_add_le (k : ℝ) 1
  dsimp [cone]
  rw [hd]
  nlinarith [mul_le_mul_of_nonneg_right hk hε]

theorem cone_shift_lower (L ε : ℝ) (hε : 0 ≤ ε) (a x : UnitAddCircle) (k : ℤ) :
    cone L ε a x (k-1) ≤ cone L ε a (x+a) k + ε := by
  have hd : dist x ((k-1) • a) = dist (x+a) (k • a) := by
    have hh := dist_add_right x ((k-1) • a) a
    simpa [sub_zsmul, sub_add_cancel] using hh.symm
  have hk : |((k-1 : ℤ) : ℝ)| ≤ |(k : ℝ)| + 1 := by
    push_cast
    simpa using abs_sub (k : ℝ) 1
  dsimp [cone]
  rw [hd]
  nlinarith [mul_le_mul_of_nonneg_right hk hε]

theorem envelope_increment (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : |envelope L ε a (x+a) - envelope L ε a x| ≤ ε := by
  have hp : envelope L ε a (x+a) - ε ≤ envelope L ε a x := by
    apply le_ciInf
    intro k
    have h1 := envelope_le_cone L ε hL hε a (x+a) (k+1)
    have h2 := cone_shift_upper L ε hε a x k
    linarith
  have hm : envelope L ε a x - ε ≤ envelope L ε a (x+a) := by
    apply le_ciInf
    intro k
    have h1 := envelope_le_cone L ε hL hε a x (k-1)
    have h2 := cone_shift_lower L ε hε a x k
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem envelope_reflection (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : envelope L ε (-a) x = envelope L ε a x := by
  have aux : ∀ b : UnitAddCircle, envelope L ε (-b) x ≤ envelope L ε b x := by
    intro b
    apply le_ciInf
    intro k
    have h := envelope_le_cone L ε hL hε (-b) x (-k)
    simpa [cone] using h
  apply le_antisymm (aux a)
  simpa using aux (-a)

def admissible (L α ε : ℝ) (P : ℝ → ℝ) : Prop :=
  Function.Periodic P 1 ∧ P 0 = 0 ∧
  (∀ x y, |P x - P y| ≤ L * |x-y|) ∧
  ∀ y, |P (y+α) - P y| ≤ ε

theorem periodic_lipschitz_quotient (L : ℝ) (P : ℝ → ℝ)
    (hp : Function.Periodic P 1) (hl : ∀ x y, |P x - P y| ≤ L * |x-y|)
    (x y : ℝ) : |P x - P y| ≤ L * dist (x : UnitAddCircle) (y : UnitAddCircle) := by
  let k : ℤ := round (x-y)
  have hh : P (y+(k : ℝ)) = P y := by
    simpa using hp.int_mul k y
  have h := hl x (y+(k : ℝ))
  rw [hh] at h
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  simpa [k, sub_sub] using h

theorem envelope_lift_admissible (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    admissible L α ε (fun x : ℝ => envelope L ε (α : UnitAddCircle) (x : UnitAddCircle)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [AddCircle.coe_add_period]
  · simpa using envelope_zero L ε hL hε (α : UnitAddCircle)
  · intro x y
    exact le_trans (envelope_lipschitz L ε hL hε _ _ _)
      (mul_le_mul_of_nonneg_left (quotient_distance_le x y) hL)
  · intro y
    simpa only [AddCircle.coe_add] using envelope_increment L ε hL hε (α : UnitAddCircle) (y : UnitAddCircle)

#print axioms envelope_nonnegative
#print axioms envelope_le_half
#print axioms envelope_zero
#print axioms envelope_lipschitz
#print axioms envelope_continuous
#print axioms envelope_increment
#print axioms envelope_reflection
#print axioms periodic_lipschitz_quotient
#print axioms envelope_lift_admissible

theorem natural_increment (α ε : ℝ) (P : ℝ → ℝ)
    (hi : ∀ y, |P (y+α)-P y| ≤ ε) (n : ℕ) (x : ℝ) :
    |P (x+(n : ℝ)*α)-P x| ≤ (n : ℝ)*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x+((n+1 : ℕ) : ℝ)*α = (x+(n : ℝ)*α)+α := by push_cast; ring
    rw [he]
    calc
      |P ((x+(n : ℝ)*α)+α)-P x| ≤
          |P ((x+(n : ℝ)*α)+α)-P (x+(n : ℝ)*α)| + |P (x+(n : ℝ)*α)-P x| := abs_sub_le _ _ _
      _ ≤ ε+(n : ℝ)*ε := add_le_add (hi _) ih
      _ = ((n+1 : ℕ) : ℝ)*ε := by push_cast; ring

theorem integer_increment (α ε : ℝ) (P : ℝ → ℝ) (hp : P 0 = 0)
    (hi : ∀ y, |P (y+α)-P y| ≤ ε) (k : ℤ) :
    |P ((k : ℝ)*α)| ≤ |(k : ℝ)| * ε := by
  cases k with
  | ofNat n =>
    simpa [hp] using natural_increment α ε P hi n 0
  | negSucc n =>
    have h := natural_increment α ε P hi (n+1) (-((n+1 : ℕ) : ℝ)*α)
    have he : -((n+1 : ℕ) : ℝ)*α+((n+1 : ℕ) : ℝ)*α = 0 := by ring
    rw [he,hp,zero_sub,abs_neg] at h
    rw [Int.cast_negSucc, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)]
    exact h

theorem compatible_pointwise_envelope (L α ε : ℝ) (P : ℝ → ℝ)
    (h : admissible L α ε P) (x : ℝ) :
    |P x| ≤ envelope L ε (α : UnitAddCircle) (x : UnitAddCircle) := by
  apply le_ciInf
  intro k
  have hp := periodic_lipschitz_quotient L P h.1 h.2.2.1 x ((k : ℝ)*α)
  have hi := integer_increment α ε P h.2.1 h.2.2.2 k
  have ht : |P x| ≤ |P x-P ((k : ℝ)*α)|+|P ((k : ℝ)*α)| := by
    simpa using abs_sub_le (P x) (P ((k : ℝ)*α)) 0
  have he : (((k : ℝ)*α : ℝ) : UnitAddCircle) = k • (α : UnitAddCircle) := by
    rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
  rw [he] at hp
  dsimp [cone]
  linarith

noncomputable def uniformNorm (P : ℝ → ℝ) : ℝ := ⨆ x : ℝ, |P x|

noncomputable def compatibleRadius (L α ε : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ P : ℝ → ℝ, admissible L α ε P ∧ v = uniformNorm P}

theorem zero_admissible (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    admissible L α ε (fun _ => 0) := by
  refine ⟨by intro; rfl, rfl, ?_, ?_⟩
  · intro x y
    simpa using mul_nonneg hL (abs_nonneg (x-y))
  · intro y
    simpa using hε

theorem compatible_uniform_bound (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (P : ℝ → ℝ) (h : admissible L α ε P) : ∀ x, |P x| ≤ L/2 := by
  intro x
  exact (compatible_pointwise_envelope L α ε P h x).trans (envelope_le_half L ε hL hε _ _)

theorem norm_bddAbove (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (P : ℝ → ℝ) (h : admissible L α ε P) : BddAbove (Set.range (fun x => |P x|)) := by
  exact ⟨L/2, by rintro v ⟨x,rfl⟩; exact compatible_uniform_bound L α ε hL hε P h x⟩

theorem radius_set_nonempty (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    {v : ℝ | ∃ P : ℝ → ℝ, admissible L α ε P ∧ v = uniformNorm P}.Nonempty := by
  exact ⟨uniformNorm (fun _ => 0), (fun _ => 0),zero_admissible L α ε hL hε,rfl⟩

theorem radius_set_bddAbove (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    BddAbove {v : ℝ | ∃ P : ℝ → ℝ, admissible L α ε P ∧ v = uniformNorm P} := by
  refine ⟨L/2, ?_⟩
  rintro v ⟨P,h,rfl⟩
  exact ciSup_le (compatible_uniform_bound L α ε hL hε P h)

theorem compatible_radius_eq_max (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    ∃ x₀ : UnitAddCircle, (∀ x, envelope L ε (α : UnitAddCircle) x ≤ envelope L ε (α : UnitAddCircle) x₀) ∧
      compatibleRadius L α ε = envelope L ε (α : UnitAddCircle) x₀ := by
  obtain ⟨x₀,_,hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set UnitAddCircle).Nonempty)
    (envelope_continuous L ε hL hε (α : UnitAddCircle)).continuousOn
  have hm : ∀ x, envelope L ε (α : UnitAddCircle) x ≤ envelope L ε (α : UnitAddCircle) x₀ :=
    fun x => hx (Set.mem_univ x)
  refine ⟨x₀,hm,le_antisymm ?_ ?_⟩
  · apply csSup_le (radius_set_nonempty L α ε hL hε)
    rintro v ⟨P,h,rfl⟩
    apply ciSup_le
    intro x
    exact (compatible_pointwise_envelope L α ε P h x).trans (hm _)
  · let P : ℝ → ℝ := fun x => envelope L ε (α : UnitAddCircle) (x : UnitAddCircle)
    have hP : admissible L α ε P := envelope_lift_admissible L α ε hL hε
    have hv : uniformNorm P ≤ compatibleRadius L α ε :=
      le_csSup (radius_set_bddAbove L α ε hL hε) ⟨P,hP,rfl⟩
    obtain ⟨x,_,rfl⟩ := AddCircle.eq_coe_Ico x₀
    have hh := le_ciSup (norm_bddAbove L α ε hL hε P hP) x
    change |envelope L ε (α : UnitAddCircle) (x : UnitAddCircle)| ≤ uniformNorm P at hh
    rw [abs_of_nonneg (envelope_nonnegative L ε hL hε _ _)] at hh
    exact hh.trans hv

#print axioms natural_increment
#print axioms integer_increment
#print axioms compatible_pointwise_envelope
#print axioms norm_bddAbove
#print axioms radius_set_nonempty
#print axioms radius_set_bddAbove
#print axioms compatible_radius_eq_max

theorem uniform_finite_minimum (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a x : UnitAddCircle, ∃ k : ℤ, |k| ≤ (N : ℤ) ∧ envelope L ε a x = cone L ε a x k := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (L / (2*ε))
  have hNε : L/2 < (N : ℝ)*ε := by
    have := (div_lt_iff₀ (show 0 < 2*ε by positivity)).mp hN
    nlinarith
  refine ⟨N, ?_⟩
  intro a x
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have h0 : (0 : ℤ) ∈ I := by simp [I]
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image I (cone L ε a x) ⟨0,h0⟩
  have hz : cone L ε a x k ≤ L/2 := by
    have h := hmin 0 h0
    have hd : dist x 0 ≤ (1 : ℝ)/2 := by
      simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := x) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hd hL
    simp only [cone, Int.cast_zero, abs_zero, zero_mul, zero_zsmul, zero_add] at h
    change |(k : ℝ)| * ε + L * dist x (k • a) ≤ L/2
    linarith
  have hall : ∀ j : ℤ, cone L ε a x k ≤ cone L ε a x j := by
    intro j
    by_cases hj : j ∈ I
    · exact hmin j hj
    · have hn : (N : ℤ) < |j| := by
        apply lt_of_not_ge
        intro hb
        exact hj (Finset.mem_Icc.mpr (abs_le.mp hb))
      have hnR : (N : ℝ) < |(j : ℝ)| := by exact_mod_cast hn
      have ht := mul_lt_mul_of_pos_right hnR hε
      have hd := mul_nonneg hL (show 0 ≤ dist x (j • a) from dist_nonneg)
      dsimp [cone] at hz ⊢
      linarith
  exact ⟨k, abs_le.mpr (Finset.mem_Icc.mp hk), le_antisymm (envelope_le_cone L ε hL hε.le a x k) (le_ciInf hall)⟩

theorem finite_minimum (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε)
    (a x : UnitAddCircle) : ∃ k : ℤ, envelope L ε a x = cone L ε a x k := by
  obtain ⟨N,hN⟩ := uniform_finite_minimum L ε hL hε
  obtain ⟨k,_,hk⟩ := hN a x
  exact ⟨k,hk⟩

theorem cone_scale (L ε : ℝ) (hL : 0 < L) (a x : UnitAddCircle) (k : ℤ) :
    cone L ε a x k = L * cone 1 (ε/L) a x k := by
  dsimp [cone]
  field_simp

theorem envelope_scale (L ε : ℝ) (hL : 0 < L) (hε : 0 ≤ ε)
    (a x : UnitAddCircle) : envelope L ε a x = L * envelope 1 (ε/L) a x := by
  have he : 0 ≤ ε/L := div_nonneg hε hL.le
  apply le_antisymm
  · have h : envelope L ε a x / L ≤ envelope 1 (ε/L) a x := by
      apply le_ciInf
      intro k
      apply (div_le_iff₀ hL).mpr
      have hk := envelope_le_cone L ε hL.le hε a x k
      rw [cone_scale L ε hL] at hk
      simpa only [mul_comm] using hk
    exact (div_le_iff₀ hL).mp h |>.trans_eq (mul_comm _ _)
  · apply le_ciInf
    intro k
    rw [cone_scale L ε hL]
    exact mul_le_mul_of_nonneg_left (envelope_le_cone 1 (ε/L) (by norm_num) he a x k) hL.le

theorem envelope_bound_iff_covers (L ε R : ℝ) (hL : 0 < L) (hε : 0 < ε)
    (a : UnitAddCircle) : (∀ x, envelope L ε a x ≤ L*R) ↔ Covers a (ε/L) R := by
  constructor
  · intro h x
    obtain ⟨k,hk⟩ := finite_minimum L ε hL.le hε a x
    refine ⟨k,?_⟩
    have hx := h x
    rw [hk,cone_scale L ε hL] at hx
    have hh := le_of_mul_le_mul_left hx hL
    simpa [cone] using hh
  · intro h x
    obtain ⟨k,hk⟩ := h x
    calc
      envelope L ε a x ≤ cone L ε a x k := envelope_le_cone L ε hL.le hε.le a x k
      _ = L * cone 1 (ε/L) a x k := cone_scale L ε hL a x k
      _ ≤ L*R := mul_le_mul_of_nonneg_left (by simpa [cone] using hk) hL.le

theorem radius_bound_iff_covers (L α ε R : ℝ) (hL : 0 < L) (hε : 0 < ε) :
    compatibleRadius L α ε ≤ L*R ↔ Covers (α : UnitAddCircle) (ε/L) R := by
  obtain ⟨x₀,hmax,he⟩ := compatible_radius_eq_max L α ε hL.le hε.le
  rw [he, ← envelope_bound_iff_covers L ε R hL hε]
  exact ⟨fun h x => (hmax x).trans h,fun h => h x₀⟩

theorem function_class_optimal_design (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n)
    (hl : 1/(2*((n:ℝ)+1)^2) ≤ ε/L) (hu : ε/L ≤ 1/(2*(n:ℝ)^2)) :
    compatibleRadius L (load n (ε/L)) ε = L*radius n (ε/L) ∧
      ∀ α : ℝ, L*radius n (ε/L) ≤ compatibleRadius L α ε := by
  have lower : ∀ α : ℝ, L*radius n (ε/L) ≤ compatibleRadius L α ε := by
    intro α
    have hc : Covers (α : UnitAddCircle) (ε/L) (compatibleRadius L α ε/L) := by
      apply (radius_bound_iff_covers L α ε _ hL hε).mp
      rw [mul_div_cancel₀ _ (ne_of_gt hL)]
    have hb := uniform_cover_radius_lower n (ε/L) (compatibleRadius L α ε/L) hn hl hu (α : UnitAddCircle) hc
    have hh := (le_div_iff₀ hL).mp hb
    simpa only [mul_comm] using hh
  refine ⟨le_antisymm ?_ (lower _),lower⟩
  apply (radius_bound_iff_covers L _ ε _ hL hε).mpr
  exact optimal_circle_cover n (ε/L) hn (div_nonneg hε.le hL.le) hu

theorem saturated_function_radius (L α ε : ℝ) (hL : 0 < L) (hε : 0 < ε)
    (hr : (1 : ℝ)/2 ≤ ε/L) : compatibleRadius L α ε = L/2 := by
  obtain ⟨hc,hl⟩ := SPJMSAudit.saturated_optimal_design (α : UnitAddCircle) (ε/L) hr
  apply le_antisymm
  · have hh := (radius_bound_iff_covers L α ε (1/2) hL hε).mpr hc
    linarith
  · have hc' : Covers (α : UnitAddCircle) (ε/L) (compatibleRadius L α ε/L) := by
      apply (radius_bound_iff_covers L α ε _ hL hε).mp
      rw [mul_div_cancel₀ _ (ne_of_gt hL)]
    have hb := (le_div_iff₀ hL).mp (hl _ hc')
    linarith

#print axioms uniform_finite_minimum
#print axioms finite_minimum
#print axioms envelope_scale
#print axioms envelope_bound_iff_covers
#print axioms radius_bound_iff_covers
#print axioms function_class_optimal_design
#print axioms saturated_function_radius

theorem radius_reflection (L α ε : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    compatibleRadius L (1-α) ε = compatibleRadius L α ε := by
  have he : ((1-α : ℝ) : UnitAddCircle) = -(α : UnitAddCircle) := by
    rw [AddCircle.coe_sub]
    have ho : ((1 : ℝ) : UnitAddCircle) = 0 := by simp
    rw [ho, zero_sub]
  obtain ⟨x,hx,hR⟩ := compatible_radius_eq_max L (1-α) ε hL hε
  obtain ⟨y,hy,hS⟩ := compatible_radius_eq_max L α ε hL hε
  rw [he] at hx hR
  simp only [envelope_reflection L ε hL hε] at hx hR
  rw [hR,hS]
  exact le_antisymm (hy x) (hx y)

theorem reflected_function_design (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n)
    (hl : 1/(2*((n:ℝ)+1)^2) ≤ ε/L) (hu : ε/L ≤ 1/(2*(n:ℝ)^2)) :
    compatibleRadius L (1-load n (ε/L)) ε = L*radius n (ε/L) := by
  rw [radius_reflection L _ ε hL.le hε.le]
  exact (function_class_optimal_design L ε hL hε n hn hl hu).1

theorem finite_control_increment (L α ε h : ℝ) (hL : 0 ≤ L)
    (P : ℝ → ℝ) (hp : Function.Periodic P 1)
    (hl : ∀ x y, |P x-P y| ≤ L * |x-y|) (C : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ C, dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ h)
    (hsample : ∀ y ∈ C, |P (y+α)-P y| ≤ ε) :
    ∀ x, |P (x+α)-P x| ≤ ε+2*L*h := by
  intro x
  obtain ⟨y,hy,hd⟩ := hcover x
  have h1 := periodic_lipschitz_quotient L P hp hl (x+α) (y+α)
  have h2 := periodic_lipschitz_quotient L P hp hl x y
  have h3 := hsample y hy
  have he : dist ((x+α : ℝ) : UnitAddCircle) ((y+α : ℝ) : UnitAddCircle) =
      dist (x : UnitAddCircle) (y : UnitAddCircle) := by
    simp only [AddCircle.coe_add]
    exact dist_add_right _ _ _
  rw [he] at h1
  have ht1 := abs_sub_le (P (x+α)) (P (y+α)) (P x)
  have ht2 := abs_sub_le (P (y+α)) (P y) (P x)
  rw [abs_sub_comm (P y) (P x)] at ht2
  nlinarith [mul_le_mul_of_nonneg_left hd hL]

theorem finite_control_radius (L α ε h : ℝ) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hh : 0 ≤ h)
    (P : ℝ → ℝ) (hp : Function.Periodic P 1) (hzero : P 0 = 0)
    (hl : ∀ x y, |P x-P y| ≤ L * |x-y|) (C : Set ℝ)
    (hcover : ∀ x : ℝ, ∃ y ∈ C, dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ h)
    (hsample : ∀ y ∈ C, |P (y+α)-P y| ≤ ε) :
    uniformNorm P ≤ compatibleRadius L α (ε+2*L*h) := by
  have hn : 0 ≤ ε+2*L*h := by positivity
  apply le_csSup (radius_set_bddAbove L α _ hL hn)
  exact ⟨P,⟨hp,hzero,hl,finite_control_increment L α ε h hL P hp hl C hcover hsample⟩,rfl⟩

#print axioms radius_reflection
#print axioms reflected_function_design
#print axioms finite_control_increment
#print axioms finite_control_radius

theorem zsmul_distance_bound (k : ℤ) (a b : UnitAddCircle) :
    dist (k • a) (k • b) ≤ |(k : ℝ)| * dist a b := by
  rw [dist_eq_norm, ← zsmul_sub, dist_eq_norm]
  simpa only [Int.norm_eq_abs] using norm_zsmul_le k (a-b)

theorem parameter_distance_bound (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a b x : UnitAddCircle,
      envelope L ε a x ≤ envelope L ε b x + (L*(N : ℝ))*dist a b := by
  obtain ⟨N,hN⟩ := uniform_finite_minimum L ε hL hε
  refine ⟨N,?_⟩
  intro a b x
  obtain ⟨k,hk,hmin⟩ := hN b x
  have hkR : |(k : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hk
  have hz := zsmul_distance_bound k b a
  rw [dist_comm b a] at hz
  have hmul := mul_le_mul_of_nonneg_right hkR (show 0 ≤ dist a b from dist_nonneg)
  have ht := dist_triangle x (k • b) (k • a)
  have hcost := mul_le_mul_of_nonneg_left (show dist x (k • a) ≤ dist x (k • b)+(N : ℝ)*dist a b by linarith) hL
  have hc := envelope_le_cone L ε hL hε.le a x k
  rw [hmin]
  dsimp [cone] at hc ⊢
  nlinarith

theorem radius_lipschitz_parameter (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ K : NNReal, LipschitzWith K (fun α : ℝ => compatibleRadius L α ε) := by
  obtain ⟨N,hN⟩ := parameter_distance_bound L ε hL hε
  have hK : 0 ≤ L*(N : ℝ) := mul_nonneg hL (Nat.cast_nonneg N)
  refine ⟨⟨L*(N : ℝ),hK⟩,LipschitzWith.of_le_add_mul _ ?_⟩
  intro α β
  obtain ⟨x,_,hx⟩ := compatible_radius_eq_max L α ε hL hε.le
  obtain ⟨y,hy,hR⟩ := compatible_radius_eq_max L β ε hL hε.le
  have hh := hN (α : UnitAddCircle) (β : UnitAddCircle) x
  have hg := mul_le_mul_of_nonneg_left (quotient_distance_le α β) hK
  rw [hx,hR]
  change envelope L ε (α : UnitAddCircle) x ≤ envelope L ε (β : UnitAddCircle) y + (L*(N : ℝ))*dist α β
  rw [Real.dist_eq]
  linarith [hy x]

theorem radius_continuous_parameter (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    Continuous (fun α : ℝ => compatibleRadius L α ε) := by
  obtain ⟨K,hK⟩ := radius_lipschitz_parameter L ε hL hε
  exact hK.continuous

#print axioms parameter_distance_bound
#print axioms radius_lipschitz_parameter
#print axioms radius_continuous_parameter

end SPJMSEnvelope
