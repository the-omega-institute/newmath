import BEDC.Derived.PythagoreanUp
import BedcMathlibBridge.Constructive.Gaussian
import Mathlib.NumberTheory.PythagoreanTriples

/-!
Pythagorean equation correspondence.

The bridge surface is only the integer equation predicate.  Mathlib's
classification theorem for Pythagorean triples is deliberately outside this
export, since its proof imports quotient and choice footprint.
-/

namespace BedcMathlibBridge.Constructive.Pythagorean

def toInt (x : BEDC.Derived.PythagoreanUp.Z) : _root_.Int :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt x

theorem toInt_add (x y : BEDC.Derived.PythagoreanUp.Z) :
    toInt (BEDC.Derived.PythagoreanUp.Zadd x y) = toInt x + toInt y :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_add x y

theorem toInt_mul (x y : BEDC.Derived.PythagoreanUp.Z) :
    toInt (BEDC.Derived.PythagoreanUp.Zmul x y) = toInt x * toInt y :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_mul x y

theorem rel_iff {x y : BEDC.Derived.PythagoreanUp.Z} :
    BEDC.Derived.PythagoreanUp.Zeq x y ↔ toInt x = toInt y :=
  BedcMathlibBridge.Constructive.Gaussian.zRelIff

theorem isPythagorean_iff_pythagoreanTriple
    {a b c : BEDC.Derived.PythagoreanUp.Z} :
    BEDC.Derived.PythagoreanUp.IsPythagorean a b c ↔
      PythagoreanTriple (toInt a) (toInt b) (toInt c) := by
  constructor
  · intro h
    have hInt := rel_iff.mp h
    unfold BEDC.Derived.PythagoreanUp.zsq at hInt
    rw [toInt_add, toInt_mul, toInt_mul, toInt_mul] at hInt
    exact hInt
  · intro h
    apply rel_iff.mpr
    unfold BEDC.Derived.PythagoreanUp.zsq
    rw [toInt_add, toInt_mul, toInt_mul, toInt_mul]
    exact h

theorem euclidTriple_pythagoreanTriple
    (m n : BEDC.Derived.PythagoreanUp.Z) :
    PythagoreanTriple
      (toInt (BEDC.Derived.PythagoreanUp.euclidA m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidB m n))
      (toInt (BEDC.Derived.PythagoreanUp.euclidC m n)) :=
  isPythagorean_iff_pythagoreanTriple.mp
    (BEDC.Derived.PythagoreanUp.euclidTriple_isPythagorean m n)

end BedcMathlibBridge.Constructive.Pythagorean
