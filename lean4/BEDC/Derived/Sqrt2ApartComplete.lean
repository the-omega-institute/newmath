import BEDC.Derived.RationalSquareOrderUp
import BEDC.Derived.Sqrt2NonCollapseWitnessFinal

namespace BEDC.Derived.Sqrt2ApartComplete

open BEDC.Derived.RationalUp
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.Sqrt2BisectionUp
open BEDC.Derived.Sqrt2IrrationalUp
open BEDC.Derived.Sqrt2NonCollapseWitnessFinal
open BEDC.Derived.RationalSquareOrderUp

theorem sqrt2_rational_square_strict_gap (q : RatNum) :
    ratLt (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo ∨
      ratLt BEDC.Derived.BoxStreamSqrt2Up.ratTwo (ratMul q q) := by
  cases rat_sq_trichotomy q with
  | inl below =>
      exact Or.inl below
  | inr rest =>
      cases rest with
      | inl exactSquare =>
          exact False.elim (sqrt2_irrational q exactSquare)
      | inr above =>
          exact Or.inr above

theorem sqrt2Bisect_exact_square_branch_absurd (q : RatNum) :
    RatEq (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo -> False := by
  intro exactSquare
  exact sqrt2_irrational q exactSquare

def sqrt2BisectWitness_of_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseWitness :=
  sqrt2BisectBoxStreamNonCollapseWitness apart

def sqrt2Bisect_nonCollapseInvariant_of_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream :=
  sqrt2BisectBoxStreamNonCollapseInvariant apart

theorem sqrt2Bisect_no_exact_rat_retraction_of_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False :=
  sqrt2BisectBoxStream_no_exact_rat_retraction apart

end BEDC.Derived.Sqrt2ApartComplete
