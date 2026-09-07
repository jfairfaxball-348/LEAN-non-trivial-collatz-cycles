import Collatz.WordArithmetic

namespace Collatz

/-- Read a cyclic word chronologically from the canonical zero cut. -/
def cyclicWordList {n : ℕ} (w : CyclicWord n) : List Bool :=
  List.ofFn (fun i : Fin n => w (i.val : ZMod n))

@[simp]
theorem length_cyclicWordList {n : ℕ} (w : CyclicWord n) :
    (cyclicWordList w).length = n := by
  simp [cyclicWordList]

@[simp]
theorem getElem_cyclicWordList {n : ℕ} (w : CyclicWord n)
    (j : ℕ) (hj : j < (cyclicWordList w).length) :
    (cyclicWordList w)[j] = w (j : ZMod n) := by
  simp [cyclicWordList]

/-- Moving the cyclic cut agrees exactly with left rotation of the
chronological list, including the wrap at the end of the period. -/
theorem cyclicWordList_rotate {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) :
    cyclicWordList (rotate w shift) = (cyclicWordList w).rotate shift.val := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    simp [List.getElem_rotate, rotate, Nat.cast_add]

/-- Express the recursively defined linear weight as a sum of bit indicators. -/
theorem listOnes_eq_sum_map (bits : List Bool) :
    listOnes bits = (bits.map (fun b => if b = true then 1 else 0)).sum := by
  induction bits with
  | nil => simp
  | cons b bs ih => cases b <;> simp [listOnes, ih]

private theorem cyclicWordList_zmod_sum_eq_sum_fin {n : ℕ} [NeZero n]
    {α : Type*} [AddCommMonoid α] (f : ZMod n → α) :
    (∑ i : ZMod n, f i) = ∑ i : Fin n, f (i.val : ZMod n) := by
  cases n with
  | zero => exact (neZero_zero_iff_false.mp ‹_›).elim
  | succ n =>
      exact Fintype.sum_equiv (ZMod.finEquiv (n + 1)).symm.toEquiv _ _ (fun x => by
        apply congrArg f
        exact (ZMod.natCast_zmod_val x).symm)

/-- The finite list and cyclic representations count exactly the same ones. -/
@[simp]
theorem listOnes_cyclicWordList {n : ℕ} [NeZero n] (w : CyclicWord n) :
    listOnes (cyclicWordList w) = ones w := by
  classical
  rw [listOnes_eq_sum_map, cyclicWordList, List.map_ofFn, List.sum_ofFn]
  calc
    (∑ i : Fin n, if w (i.val : ZMod n) = true then 1 else 0) =
        ∑ i : ZMod n, if w i = true then 1 else 0 :=
      (cyclicWordList_zmod_sum_eq_sum_fin
        (fun i : ZMod n => if w i = true then (1 : ℕ) else 0)).symm
    _ = (Finset.univ.filter (fun i : ZMod n => w i = true)).sum
        (fun _ => (1 : ℕ)) := by rw [Finset.sum_filter]
    _ = ones w := by simp [ones]

/-- Equal-length lists whose entries can differ only in `[p,p+m)` have
identical prefixes before the window and suffixes after it. -/
theorem take_drop_eq_of_getElem_eq_outside {α : Type*} {xs ys : List α}
    {p m : ℕ} (hlen : xs.length = ys.length)
    (houtside : ∀ j (hjx : j < xs.length) (hjy : j < ys.length),
      j < p ∨ p + m ≤ j → xs[j]'hjx = ys[j]'hjy) :
    xs.take p = ys.take p ∧ xs.drop (p + m) = ys.drop (p + m) := by
  constructor
  · apply List.ext_getElem
    · simp [hlen]
    · intro j hjx hjy
      simp only [List.length_take] at hjx hjy
      simp only [List.getElem_take]
      exact houtside j (by omega) (by omega) (Or.inl (by omega))
  · apply List.ext_getElem
    · simp [hlen]
    · intro j hjx hjy
      simp only [List.length_drop] at hjx hjy
      simp only [List.getElem_drop]
      exact houtside (p + m + j) (by omega) (by omega) (Or.inr (by omega))

/-- Cut equal-length lists at a bounded difference window, retaining a common
prefix and suffix around their respective chronological middle blocks. -/
theorem shared_prefix_suffix_of_getElem_eq_outside {α : Type*}
    {xs ys : List α} {p m : ℕ} (hlen : xs.length = ys.length)
    (hwindow : p + m ≤ xs.length)
    (houtside : ∀ j (hjx : j < xs.length) (hjy : j < ys.length),
      j < p ∨ p + m ≤ j → xs[j]'hjx = ys[j]'hjy) :
    ∃ pre suffix : List α,
      pre.length = p ∧
      xs = pre ++ (xs.drop p).take m ++ suffix ∧
      ys = pre ++ (ys.drop p).take m ++ suffix := by
  obtain ⟨hprefix, hsuffix⟩ := take_drop_eq_of_getElem_eq_outside hlen houtside
  refine ⟨xs.take p, xs.drop (p + m), ?_, ?_, ?_⟩
  · simp only [List.length_take]
    omega
  · rw [List.append_assoc, List.drop_take_append_drop, List.take_append_drop]
  · rw [hprefix, hsuffix, List.append_assoc, List.drop_take_append_drop,
      List.take_append_drop]

/-- Pointwise cyclic agreement outside a chronological interval gives the
same finite prefix and suffix in the zero-cut list representation. -/
theorem cyclicWordList_take_drop_eq_of_eq_outside {n : ℕ}
    {source target : CyclicWord n} {p m : ℕ}
    (houtside : ∀ j, j < n → j < p ∨ p + m ≤ j →
      source (j : ZMod n) = target (j : ZMod n)) :
    (cyclicWordList source).take p = (cyclicWordList target).take p ∧
      (cyclicWordList source).drop (p + m) =
        (cyclicWordList target).drop (p + m) := by
  apply take_drop_eq_of_getElem_eq_outside (by simp)
  intro j hjx hjy hjoutside
  simpa using houtside j (by simpa using hjx) hjoutside

end Collatz
