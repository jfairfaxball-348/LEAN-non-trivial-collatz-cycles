import Collatz.Radius4ConnectedCoefficients
import Collatz.Cycle

namespace Collatz

/-- The full cycle denominator is coprime to six for positive exponents.
This supplies the monomial cancellation required by RL238 R4-2 internally. -/
theorem cycleDenominator_isCoprime_six {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) :
    IsCoprime (cycleDenominator A L) 6 := by
  have h23 : IsCoprime (2 : ℤ) 3 := by decide
  have hpows : IsCoprime ((2 : ℤ) ^ A) ((3 : ℤ) ^ L) := h23.pow
  have htwo : IsCoprime (cycleDenominator A L) ((2 : ℤ) ^ A) := by
    simpa only [mul_one, cycleDenominator] using
      (IsCoprime.mul_sub_left_left_iff
        (x := (3 : ℤ) ^ L) (y := (2 : ℤ) ^ A) (z := 1)).mpr hpows.symm
  have hthree : IsCoprime (cycleDenominator A L) ((3 : ℤ) ^ L) := by
    simpa only [mul_one, cycleDenominator] using
      (IsCoprime.sub_mul_left_left_iff
        (x := (2 : ℤ) ^ A) (y := (3 : ℤ) ^ L) (z := 1)).mpr hpows
  have htwo' := (IsCoprime.pow_right_iff hA).mp htwo
  have hthree' := (IsCoprime.pow_right_iff hL).mp hthree
  simpa using htwo'.mul_right hthree'

/-- Powers of two and three in an unchanged context may be cancelled from
full-denominator divisibility. -/
theorem cycleDenominator_dvd_transport_context_iff {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (a b : ℕ) (q : ℤ) :
    cycleDenominator A L ∣ (2 : ℤ) ^ a * (3 : ℤ) ^ b * q ↔
      cycleDenominator A L ∣ q := by
  have hcop : IsCoprime (cycleDenominator A L) ((2 : ℤ) * 3) := by
    simpa using cycleDenominator_isCoprime_six hA hL
  obtain ⟨h2, h3⟩ := IsCoprime.mul_right_iff.mp hcop
  have hmon : IsCoprime (cycleDenominator A L)
      ((2 : ℤ) ^ a * (3 : ℤ) ^ b) := h2.pow_right.mul_right h3.pow_right
  exact hmon.dvd_mul_left_iff

/-- The exact connected local replacement leaves divisibility of its small
coefficient by the full denominator. -/
theorem cycleDenominator_dvd_connectedFourCoefficient_of_context_difference
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L)
    (pre suffix : List Bool) (a b c : Bool)
    (hdiv : cycleDenominator A L ∣
      (wordNumerator (pre ++ [false, a, b, c, true] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [true, a, b, c, false] ++ suffix) : ℤ)) :
    cycleDenominator A L ∣ (transportConnectedFourCoefficient a b c : ℤ) := by
  rw [wordNumerator_connectedFour_context_difference] at hdiv
  exact (cycleDenominator_dvd_transport_context_iff hA hL _ _ _).mp hdiv

/-- The height-two local replacement leaves divisibility of fifteen by the
full denominator, independently of its unchanged prefix and suffix. -/
theorem cycleDenominator_dvd_fifteen_of_heightTwo_context_difference
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (pre suffix : List Bool)
    (hdiv : cycleDenominator A L ∣
      (wordNumerator (pre ++ [true, true, false, false] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [false, false, true, true] ++ suffix) : ℤ)) :
    cycleDenominator A L ∣ 15 := by
  rw [wordNumerator_heightTwo_context_difference] at hdiv
  have h := (cycleDenominator_dvd_transport_context_iff hA hL _ _ _).mp hdiv
  simpa only [dvd_neg] using h

/-- The exact finite divisor calculation in RL238 R4-2: a denominator
greater than one, coprime to six, dividing a connected local coefficient
belongs to the established eight-element list. -/
theorem transportConnected_denominator_mem {d c : ℕ}
    (hd : 1 < d) (hcoprime : d.Coprime 6)
    (hc : c ∈ ([15, 17, 21, 27, 29, 35, 47, 65] : List ℕ))
    (hdiv : d ∣ c) :
    d ∈ ([5, 7, 13, 17, 29, 35, 47, 65] : List ℕ) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have hcpos : 0 < c := by omega
  have hclt : c < 66 := by omega
  have hdlt : d < 66 := lt_of_le_of_lt (Nat.le_of_dvd hcpos hdiv) hclt
  have hdivcases :
      d ∣ 15 ∨ d ∣ 17 ∨ d ∣ 21 ∨ d ∣ 27 ∨
        d ∣ 29 ∨ d ∣ 35 ∨ d ∣ 47 ∨ d ∣ 65 := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
  have hfinite : ∀ x : Fin 66, 1 < x.val → x.val.Coprime 6 →
      (x.val ∣ 15 ∨ x.val ∣ 17 ∨ x.val ∣ 21 ∨ x.val ∣ 27 ∨
        x.val ∣ 29 ∨ x.val ∣ 35 ∨ x.val ∣ 47 ∨ x.val ∣ 65) →
      x.val ∈ ([5, 7, 13, 17, 29, 35, 47, 65] : List ℕ) := by
    decide
  exact hfinite ⟨d, hdlt⟩ hd hcoprime hdivcases

/-- Specialization to the eight directly evaluated connected four-edge
coefficients; the coefficient is not an additional arithmetic assumption. -/
theorem transportConnectedFour_denominator_mem {d : ℕ}
    (hd : 1 < d) (hcoprime : d.Coprime 6) (a b c : Bool)
    (hdiv : d ∣ transportConnectedFourCoefficient a b c) :
    d ∈ ([5, 7, 13, 17, 29, 35, 47, 65] : List ℕ) := by
  apply transportConnected_denominator_mem hd hcoprime _ hdiv
  cases a <;> cases b <;> cases c <;> decide

/-- The height-two coefficient fifteen leaves only denominator five. -/
theorem transportHeightTwo_denominator_eq_five {d : ℕ}
    (hd : 1 < d) (hcoprime : d.Coprime 6) (hdiv : d ∣ 15) :
    d = 5 := by
  have hmem := transportConnected_denominator_mem hd hcoprime
    (show 15 ∈ ([15, 17, 21, 27, 29, 35, 47, 65] : List ℕ) by decide) hdiv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hdiv
  rfl

end Collatz
