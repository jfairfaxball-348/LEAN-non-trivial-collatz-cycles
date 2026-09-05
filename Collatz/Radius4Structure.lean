import Collatz.Radius4

namespace Collatz

/-- Positions where a `true` bit of `u` becomes `false` in `v`. -/
def downMismatches {n : ℕ} [NeZero n] (u v : CyclicWord n) : ℕ :=
  (Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = false)).card

/-- Positions where a `false` bit of `u` becomes `true` in `v`. -/
def upMismatches {n : ℕ} [NeZero n] (u v : CyclicWord n) : ℕ :=
  (Finset.univ.filter (fun i : ZMod n => u i = false ∧ v i = true)).card

/-- Common true positions of two words. -/
def commonTrue {n : ℕ} [NeZero n] (u v : CyclicWord n) : ℕ :=
  (Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = true)).card

/-- The true positions of `u` partition into common true positions and
true-to-false mismatches. -/
theorem ones_eq_commonTrue_add_down {n : ℕ} [NeZero n]
    (u v : CyclicWord n) :
    ones u = commonTrue u v + downMismatches u v := by
  classical
  let both := Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = true)
  let down := Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = false)
  have hpartition :
      Finset.univ.filter (fun i : ZMod n => u i = true) = both ∪ down := by
    ext i
    cases hu : u i <;> cases hv : v i <;>
      simp [both, down, hu, hv]
  have hdisjoint : Disjoint both down := by
    refine Finset.disjoint_left.mpr ?_
    intro i hib hid
    simp [both] at hib
    simp [down] at hid
    simp [hib.2] at hid
  rw [ones, hpartition, Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- The true positions of `v` partition into common true positions and
false-to-true mismatches. -/
theorem ones_eq_commonTrue_add_up {n : ℕ} [NeZero n]
    (u v : CyclicWord n) :
    ones v = commonTrue u v + upMismatches u v := by
  classical
  let both := Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = true)
  let up := Finset.univ.filter (fun i : ZMod n => u i = false ∧ v i = true)
  have hpartition :
      Finset.univ.filter (fun i : ZMod n => v i = true) = both ∪ up := by
    ext i
    cases hu : u i <;> cases hv : v i <;>
      simp [both, up, hu, hv]
  have hdisjoint : Disjoint both up := by
    refine Finset.disjoint_left.mpr ?_
    intro i hib hiu
    simp [both] at hib
    simp [up] at hiu
    simp [hib.1] at hiu
  rw [ones, hpartition, Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- Every Hamming mismatch is uniquely either a down-mismatch or an
up-mismatch. -/
theorem hammingDistance_eq_down_add_up {n : ℕ} [NeZero n]
    (u v : CyclicWord n) :
    hammingDistance u v = downMismatches u v + upMismatches u v := by
  classical
  let down := Finset.univ.filter (fun i : ZMod n => u i = true ∧ v i = false)
  let up := Finset.univ.filter (fun i : ZMod n => u i = false ∧ v i = true)
  have hpartition :
      Finset.univ.filter (fun i : ZMod n => u i ≠ v i) = down ∪ up := by
    ext i
    cases hu : u i <;> cases hv : v i <;>
      simp [down, up, hu, hv]
  have hdisjoint : Disjoint down up := by
    refine Finset.disjoint_left.mpr ?_
    intro i hid hiu
    simp [down] at hid
    simp [up] at hiu
    simp [hid.1] at hiu
  rw [hammingDistance, hpartition, Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- Equal-weight binary words have equally many mismatches in the two
orientations. -/
theorem down_eq_up_of_ones_eq {n : ℕ} [NeZero n]
    {u v : CyclicWord n} (hones : ones u = ones v) :
    downMismatches u v = upMismatches u v := by
  have hu := ones_eq_commonTrue_add_down u v
  have hv := ones_eq_commonTrue_add_up u v
  omega

/-- Exact Hamming distance four between equal-weight binary words consists of
exactly two `true→false` and two `false→true` mismatches. -/
theorem hammingFour_directional_counts {n : ℕ} [NeZero n]
    {u v : CyclicWord n} (hones : ones u = ones v)
    (hfour : hammingDistance u v = 4) :
    downMismatches u v = 2 ∧ upMismatches u v = 2 := by
  have hdu := down_eq_up_of_ones_eq hones
  have hsum := hammingDistance_eq_down_add_up u v
  omega

/-- Rotation preserves the number of true bits. -/
theorem ones_rotate {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n) :
    ones (rotate w shift) = ones w := by
  classical
  unfold ones
  apply Finset.card_bij (fun i _ => i + shift)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa [rotate] using hi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact add_right_cancel heq
  · intro j hj
    refine ⟨j - shift, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      simpa [rotate] using hj
    · simp

/-- Radius 4 against a rotation therefore has exactly two mismatches in each
orientation; no separate equal-weight hypothesis is needed. -/
theorem radiusFour_directional_counts {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n)
    (hfour : IsRadiusFour w shift) :
    downMismatches w (rotate w shift) = 2 ∧
      upMismatches w (rotate w shift) = 2 := by
  apply hammingFour_directional_counts (ones_rotate w shift).symm
  exact (isRadiusFour_iff w shift).mp hfour

end Collatz
