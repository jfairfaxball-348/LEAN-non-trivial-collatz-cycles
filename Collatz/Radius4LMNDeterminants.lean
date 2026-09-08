import Collatz.Radius4LogDefect
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Vandermonde

namespace Collatz

/-- The analytic upper-bound primitive used by interpolation-determinant
arguments: bounding every complex entry by `x` bounds the determinant by
`card(ι)! * x^card(ι)`.  The later LMN construction must provide its specific
matrix and the complementary nonzero arithmetic lower bound. -/
theorem interpolationDeterminant_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : ℝ) (hentries : ∀ i j, ‖A i j‖ ≤ x) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * x ^ Fintype.card ι := by
  change (IsAbsoluteValue.toAbsoluteValue (‖·‖ : ℂ → ℝ)) A.det ≤
    (Fintype.card ι).factorial * x ^ Fintype.card ι
  simpa only [nsmul_eq_mul] using
    (Matrix.det_le (A := A)
      (abv := IsAbsoluteValue.toAbsoluteValue (‖·‖ : ℂ → ℝ)) hentries)

/-- The monomials used to index a two-logarithm interpolation determinant are
distinct: the exponent pair is recoverable from the prime factorizations at
two and three. -/
theorem two_three_monomial_injective {a b c d : ℕ}
    (h : 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d) : a = c ∧ b = d := by
  have htwo := congrArg (fun n : ℕ => n.factorization 2) h
  have hthree := congrArg (fun n : ℕ => n.factorization 3) h
  have hthreeAtTwo : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have htwoAtThree : (2 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  constructor
  · simpa [Nat.factorization_mul, Nat.prime_two.factorization_pow, hthreeAtTwo] using htwo
  · simpa [Nat.factorization_mul, Nat.prime_three.factorization_pow, htwoAtThree] using hthree

/-- The arithmetic lower-bound primitive for an integral interpolation
determinant.  Once a zero lemma supplies nonvanishing, its complex norm is at
least one. -/
theorem integerInterpolationDeterminant_norm_one_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) :
    1 ≤ ‖(A.map fun z => (z : ℂ)).det‖ := by
  rw [← Int.cast_det, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hdet

/-- A concrete nonzero integral interpolation determinant for distinct
two-prime exponent pairs.  This is the Vandermonde instance of the
nonvanishing mechanism required by interpolation-determinant arguments. -/
theorem twoThreeVandermonde_det_ne_zero {n : ℕ}
    (a b : Fin n → ℕ) (hinj : Function.Injective fun i => (a i, b i)) :
    (Matrix.vandermonde fun i => (2 ^ a i * 3 ^ b i : ℤ)).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  change (2 ^ a i * 3 ^ b i : ℤ) = 2 ^ a j * 3 ^ b j at hij
  have hijNat : 2 ^ a i * 3 ^ b i = 2 ^ a j * 3 ^ b j := by
    exact_mod_cast hij
  rcases two_three_monomial_injective hijNat with ⟨ha, hb⟩
  exact hinj (Prod.ext ha hb)

end Collatz
