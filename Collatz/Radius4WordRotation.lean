import Collatz.Radius4ConnectedDenominators

namespace Collatz

/-- Exact full-denominator covariance under rotation of two consecutive
blocks. This identity concerns arbitrary binary words. -/
theorem wordNumerator_blockSwap_covariance (xs ys : List Bool) :
    (2 : ℤ) ^ xs.length *
        (wordNumerator (ys ++ xs) : ℤ) -
      (3 : ℤ) ^ listOnes xs *
        (wordNumerator (xs ++ ys) : ℤ) =
    cycleDenominator
        (xs.length + ys.length) (listOnes xs + listOnes ys) *
      (wordNumerator xs : ℤ) := by
  simp only [wordNumerator_append, cycleDenominator]
  push_cast
  simp only [pow_add]
  ring

/-- Divisibility by the complete word denominator survives block rotation.
The positive total exponents allow cancellation of the prefix's power of two. -/
theorem cycleDenominator_dvd_wordNumerator_blockSwap
    (xs ys : List Bool)
    (hA : 0 < xs.length + ys.length)
    (hL : 0 < listOnes xs + listOnes ys)
    (hdiv :
      cycleDenominator
          (xs.length + ys.length) (listOnes xs + listOnes ys) ∣
        (wordNumerator (xs ++ ys) : ℤ)) :
    cycleDenominator
        (xs.length + ys.length) (listOnes xs + listOnes ys) ∣
      (wordNumerator (ys ++ xs) : ℤ) := by
  have hdiff :
      cycleDenominator
          (xs.length + ys.length) (listOnes xs + listOnes ys) ∣
        (2 : ℤ) ^ xs.length *
            (wordNumerator (ys ++ xs) : ℤ) -
          (3 : ℤ) ^ listOnes xs *
            (wordNumerator (xs ++ ys) : ℤ) := by
    rw [wordNumerator_blockSwap_covariance]
    exact dvd_mul_right _ _
  have hsource :
      cycleDenominator
          (xs.length + ys.length) (listOnes xs + listOnes ys) ∣
        (3 : ℤ) ^ listOnes xs *
          (wordNumerator (xs ++ ys) : ℤ) :=
    dvd_mul_of_dvd_right hdiv ((3 : ℤ) ^ listOnes xs)
  have hscaled :
      cycleDenominator
          (xs.length + ys.length) (listOnes xs + listOnes ys) ∣
        (2 : ℤ) ^ xs.length *
          (wordNumerator (ys ++ xs) : ℤ) := by
    simpa only [sub_add_cancel] using dvd_add hdiff hsource
  apply
    (cycleDenominator_dvd_transport_context_iff
      hA hL xs.length 0 (wordNumerator (ys ++ xs) : ℤ)).mp
  simpa only [pow_zero, mul_one] using hscaled

/-- Divisibility by the exact full denominator survives any cyclic rotation
of an arbitrary binary list with positive length and weight. -/
theorem cycleDenominator_dvd_wordNumerator_rotate
    (bits : List Bool) (shift : ℕ)
    (hA : 0 < bits.length) (hL : 0 < listOnes bits)
    (hdiv : cycleDenominator bits.length (listOnes bits) ∣
      (wordNumerator bits : ℤ)) :
    cycleDenominator bits.length (listOnes bits) ∣
      (wordNumerator (bits.rotate shift) : ℤ) := by
  let xs := bits.take (shift % bits.length)
  let ys := bits.drop (shift % bits.length)
  have hsplit : xs ++ ys = bits := List.take_append_drop _ _
  have hlength : xs.length + ys.length = bits.length := by
    simpa only [List.length_append] using congrArg List.length hsplit
  have hones : listOnes xs + listOnes ys = listOnes bits := by
    simpa only [listOnes_append] using congrArg listOnes hsplit
  have hrot :=
    cycleDenominator_dvd_wordNumerator_blockSwap xs ys
      (by simpa only [hlength] using hA)
      (by simpa only [hones] using hL)
      (by simpa only [hlength, hones, hsplit] using hdiv)
  rw [List.rotate_eq_drop_append_take_mod]
  change cycleDenominator bits.length (listOnes bits) ∣
    (wordNumerator (ys ++ xs) : ℤ)
  simpa only [hlength, hones] using hrot

end Collatz
