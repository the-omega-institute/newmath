import BEDC.Derived.Sqrt2BisectionUp
import BEDC.Derived.Sqrt2IrrationalUp

namespace BEDC.Derived.Sqrt2NonCollapseWitnessFinal

open BEDC.Derived.RationalUp
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.Sqrt2BisectionUp
open BEDC.Derived.Sqrt2IrrationalUp

def sqrt2BisectIntervalRatSeparatedBool (k : Nat) (q : RatNum) : Bool :=
  QIntervalRatSeparatedBool (sqrt2BisectReInterval k) q

def sqrt2BisectIntervalRatSeparated (k : Nat) (q : RatNum) : Prop :=
  QIntervalRatSeparated (sqrt2BisectReInterval k) q

theorem sqrt2BisectIntervalRatSeparatedBool_sound {k : Nat} {q : RatNum} :
    sqrt2BisectIntervalRatSeparatedBool k q = true ->
      sqrt2BisectIntervalRatSeparated k q := by
  intro h
  exact QIntervalRatSeparatedBool_sound h

theorem sqrt2BisectIntervalRatSeparatedBool_complete {k : Nat} {q : RatNum} :
    sqrt2BisectIntervalRatSeparated k q ->
      sqrt2BisectIntervalRatSeparatedBool k q = true := by
  intro h
  exact QIntervalRatSeparatedBool_complete h

def sqrt2BisectRatOutside_of_bool {k : Nat} {q : RatNum} :
    sqrt2BisectIntervalRatSeparatedBool k q = true ->
      Sqrt2BisectRatOutside q := by
  intro h
  exact
    { precision := k
      separated := sqrt2BisectIntervalRatSeparatedBool_sound h }

def sqrt2BisectRatOutside_to_box_apart {q : RatNum} :
    Sqrt2BisectRatOutside q ->
      BoxStreamApart sqrt2BisectGauge sqrt2BisectBoxStream q := by
  intro outside
  exact Sqrt2BisectRatOutside.to_box_apart outside

def sqrt2BisectBoxStreamNonCollapseWitness
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseWitness :=
  sqrt2BisectApartnessBridgeToWitness apart

def sqrt2BisectBoxStreamNonCollapseInvariant
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream := by
  intro q
  exact Sqrt2BisectRatOutside.to_box_apart (apart q)

theorem sqrt2BisectBoxStream_no_exact_rat_retraction
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False := by
  intro retraction
  exact sqrt2BisectApartnessBridge_no_rat_retraction apart retraction

theorem sqrt2_irrational_blocks_exact_square :
    forall q : RatNum,
      RatEq (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo -> False := by
  intro q h
  exact sqrt2_irrational q h

end BEDC.Derived.Sqrt2NonCollapseWitnessFinal
