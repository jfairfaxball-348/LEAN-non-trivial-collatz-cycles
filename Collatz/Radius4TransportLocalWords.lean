import Collatz.CyclicWordList
import Collatz.Radius4TransportConnectedBits

namespace Collatz

private theorem cyclicWordList_window_eq_ofFn {n : ℕ} (w : CyclicWord n)
    {p m : ℕ} (hwindow : p + m ≤ n) :
    ((cyclicWordList w).drop p).take m =
      List.ofFn (fun i : Fin m => w ((p + i.val : ℕ) : ZMod n)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_cyclicWordList, List.length_ofFn]
    omega
  · intro j hj₁ hj₂
    simp

private theorem cyclicWordList_window_four {n : ℕ} (w : CyclicWord n)
    {p : ℕ} (hwindow : p + 4 ≤ n) :
    ((cyclicWordList w).drop p).take 4 =
      [w (p : ZMod n), w ((p + 1 : ℕ) : ZMod n),
        w ((p + 2 : ℕ) : ZMod n), w ((p + 3 : ℕ) : ZMod n)] := by
  simpa [List.ofFn_succ] using cyclicWordList_window_eq_ofFn w hwindow

private theorem cyclicWordList_window_five {n : ℕ} (w : CyclicWord n)
    {p : ℕ} (hwindow : p + 5 ≤ n) :
    ((cyclicWordList w).drop p).take 5 =
      [w (p : ZMod n), w ((p + 1 : ℕ) : ZMod n),
        w ((p + 2 : ℕ) : ZMod n), w ((p + 3 : ℕ) : ZMod n),
        w ((p + 4 : ℕ) : ZMod n)] := by
  simpa [List.ofFn_succ] using cyclicWordList_window_eq_ofFn w hwindow

/-- The connected unit-height branch supplies complete chronological lists
with exactly the same prefix and suffix around `1abc0 ↔ 0abc1`. -/
theorem transportConnectedFour_exists_word_context_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target)
    (hcost : transportCostAtCut source target 0 = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target 0 (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths source target 0).Perm [4]) :
    ∃ (pre suffix : List Bool) (b a₁ a₂ a₃ : Bool),
      cyclicWordList source = pre ++ [b, a₁, a₂, a₃, !b] ++ suffix ∧
      cyclicWordList target = pre ++ [!b, a₁, a₂, a₃, b] ++ suffix := by
  obtain ⟨p, b, hp, h0s, h0t, h4s, h4t, hmiddle, houtside⟩ :=
    transportConnectedFour_local_bits_of_cost_four hones 0 hcost hunit hconnected
  simp only [zero_add] at h0s h0t h4s h4t hmiddle houtside
  have hwindow : p + 5 ≤ n := by omega
  have hout : ∀ j (hs : j < (cyclicWordList source).length)
      (ht : j < (cyclicWordList target).length),
      j < p ∨ p + 5 ≤ j →
        (cyclicWordList source)[j]'hs = (cyclicWordList target)[j]'ht := by
    intro j hs ht hj
    simpa only [getElem_cyclicWordList] using houtside j (by simpa using hs) hj
  obtain ⟨pre, suffix, _hpre, hs, ht⟩ :=
    shared_prefix_suffix_of_getElem_eq_outside (p := p) (m := 5)
      (by simp : (cyclicWordList source).length = (cyclicWordList target).length)
      (by simpa only [length_cyclicWordList] using hwindow) hout
  have h1 := hmiddle (p + 1) (by omega) (by omega)
  have h2 := hmiddle (p + 2) (by omega) (by omega)
  have h3 := hmiddle (p + 3) (by omega) (by omega)
  rw [cyclicWordList_window_five source hwindow, h0s, h4s] at hs
  rw [cyclicWordList_window_five target hwindow, h0t, h4t, ← h1, ← h2, ← h3] at ht
  exact ⟨pre, suffix, b, source ((p + 1 : ℕ) : ZMod n),
    source ((p + 2 : ℕ) : ZMod n), source ((p + 3 : ℕ) : ZMod n), hs, ht⟩

/-- The rigid height-two branch supplies complete chronological lists with
the same prefix and suffix around `0011 ↔ 1100`. -/
theorem transportHeightTwo_exists_word_context_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target)
    (hcost : transportCostAtCut source target 0 = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude source target 0 k = 2) :
    ∃ (pre suffix : List Bool) (b : Bool),
      cyclicWordList source = pre ++ [b, b, !b, !b] ++ suffix ∧
      cyclicWordList target = pre ++ [!b, !b, b, b] ++ suffix := by
  obtain ⟨hkgt, hksucc, _, _, _⟩ :=
    transportHeightTwo_rigid_of_cost_four hones 0 hcost hkpos hklt hk
  obtain ⟨b, h0s, h1s, h2s, h3s, h0t, h1t, h2t, h3t⟩ :=
    transportHeightTwo_local_bits_of_cost_four hones 0 hcost hkpos hklt hk
  simp only [zero_add] at h0s h1s h2s h3s h0t h1t h2t h3t
  let p := k - 2
  have hp1 : p + 1 = k - 1 := by dsimp [p]; omega
  have hp2 : p + 2 = k := by dsimp [p]; omega
  have hp3 : p + 3 = k + 1 := by dsimp [p]; omega
  have hwindow : p + 4 ≤ n := by dsimp [p]; omega
  have hout : ∀ j (hs : j < (cyclicWordList source).length)
      (ht : j < (cyclicWordList target).length),
      j < p ∨ p + 4 ≤ j →
        (cyclicWordList source)[j]'hs = (cyclicWordList target)[j]'ht := by
    intro j hs ht hj
    have hjout : j < k - 2 ∨ k + 2 ≤ j := by dsimp [p] at hj; omega
    have hbits := transportHeightTwo_bits_eq_outside_of_cost_four hones 0 hcost
      hkpos hklt hk (j := j) (by simpa using hs) hjout
    simpa only [zero_add, getElem_cyclicWordList] using hbits
  obtain ⟨pre, suffix, _hpre, hs, ht⟩ :=
    shared_prefix_suffix_of_getElem_eq_outside (p := p) (m := 4)
      (by simp : (cyclicWordList source).length = (cyclicWordList target).length)
      (by simpa only [length_cyclicWordList] using hwindow) hout
  rw [cyclicWordList_window_four source hwindow, hp1, hp2, hp3,
    h0s, h1s, h2s, h3s] at hs
  rw [cyclicWordList_window_four target hwindow, hp1, hp2, hp3,
    h0t, h1t, h2t, h3t] at ht
  exact ⟨pre, suffix, b, hs, ht⟩

end Collatz
