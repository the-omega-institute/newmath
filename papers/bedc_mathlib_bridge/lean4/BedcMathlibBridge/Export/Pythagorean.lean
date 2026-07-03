import BedcMathlibBridge.Constructive.Pythagorean

/-!
Export witness for the Pythagorean equation correspondence.

The witness records the canonical readback from BEDC integer rows to mathlib
integers and the exact predicate equivalence with `PythagoreanTriple`.
-/

namespace BedcMathlibBridge.Export.Pythagorean

open BedcMathlibBridge.Constructive.Pythagorean

structure PythagoreanExportWitness where
  toInt : BEDC.Derived.PythagoreanUp.Z -> _root_.Int
  toInt_apply : ∀ z : BEDC.Derived.PythagoreanUp.Z,
    toInt z = BedcMathlibBridge.Constructive.Pythagorean.toInt z
  predicate_iff : ∀ a b c : BEDC.Derived.PythagoreanUp.Z,
    BEDC.Derived.PythagoreanUp.IsPythagorean a b c ↔
      PythagoreanTriple (toInt a) (toInt b) (toInt c)
  euclid_apply : ∀ m n : BEDC.Derived.PythagoreanUp.Z,
    PythagoreanTriple
      (toInt (BEDC.Derived.PythagoreanUp.euclidA m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidB m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidC m n))

def pythagoreanExport : PythagoreanExportWitness where
  toInt := BedcMathlibBridge.Constructive.Pythagorean.toInt
  toInt_apply := by
    intro z
    rfl
  predicate_iff := by
    intro a b c
    exact
      BedcMathlibBridge.Constructive.Pythagorean.isPythagorean_iff_pythagoreanTriple
  euclid_apply := by
    intro m n
    exact BedcMathlibBridge.Constructive.Pythagorean.euclidTriple_pythagoreanTriple m n

theorem isPythagorean_iff_pythagoreanTriple
    {a b c : BEDC.Derived.PythagoreanUp.Z} :
    BEDC.Derived.PythagoreanUp.IsPythagorean a b c ↔
      PythagoreanTriple (toInt a) (toInt b) (toInt c) :=
  BedcMathlibBridge.Constructive.Pythagorean.isPythagorean_iff_pythagoreanTriple

theorem euclidTriple_pythagoreanTriple
    (m n : BEDC.Derived.PythagoreanUp.Z) :
    PythagoreanTriple
      (toInt (BEDC.Derived.PythagoreanUp.euclidA m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidB m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidC m n)) :=
  BedcMathlibBridge.Constructive.Pythagorean.euclidTriple_pythagoreanTriple m n

end BedcMathlibBridge.Export.Pythagorean
