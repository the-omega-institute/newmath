import BedcMathlibBridge.Export.Int
import Mathlib.Algebra.EuclideanDomain.Int

namespace BedcMathlibBridge.Export.IntProbe

open BedcMathlibBridge.Constructive.Int

theorem cInt_add_comm_probe (x y : CInt) : x + y = y + x := by
  exact
    CInt.canonical_ext
      ((CInt.toInt_add x y).trans
        ((_root_.Int.add_comm x.toInt y.toInt).trans
          (CInt.toInt_add y x).symm))

theorem cInt_mul_comm_probe (x y : CInt) : x * y = y * x := by
  exact
    CInt.canonical_ext
      ((CInt.toInt_mul x y).trans
        ((_root_.Int.mul_comm x.toInt y.toInt).trans
          (CInt.toInt_mul y x).symm))

theorem cInt_left_distrib_probe (x y z : CInt) :
    x * (y + z) = x * y + x * z := by
  exact
    CInt.canonical_ext
      ((CInt.toInt_mul x (y + z)).trans
        ((congrArg (fun t => x.toInt * t) (CInt.toInt_add y z)).trans
          ((_root_.Int.mul_add x.toInt y.toInt z.toInt).trans
            ((congrArg₂ (fun a b => a + b) (CInt.toInt_mul x y).symm
                (CInt.toInt_mul x z).symm).trans
              (CInt.toInt_add (x * y) (x * z)).symm))))

theorem cInt_commRing_constructive_probe :
    (∀ x y : CInt, x + y = y + x) ∧
      (∀ x y : CInt, x * y = y * x) ∧
      (∀ x y z : CInt, x * (y + z) = x * y + x * z) := by
  exact
    ⟨fun x y =>
        CInt.canonical_ext
          ((CInt.toInt_add x y).trans
            ((_root_.Int.add_comm x.toInt y.toInt).trans
              (CInt.toInt_add y x).symm)),
      fun x y =>
        CInt.canonical_ext
          ((CInt.toInt_mul x y).trans
            ((_root_.Int.mul_comm x.toInt y.toInt).trans
              (CInt.toInt_mul y x).symm)),
      fun x y z =>
        CInt.canonical_ext
          ((CInt.toInt_mul x (y + z)).trans
            ((congrArg (fun t => x.toInt * t) (CInt.toInt_add y z)).trans
              ((_root_.Int.mul_add x.toInt y.toInt z.toInt).trans
                ((congrArg₂ (fun a b => a + b) (CInt.toInt_mul x y).symm
                    (CInt.toInt_mul x z).symm).trans
                  (CInt.toInt_add (x * y) (x * z)).symm))))⟩

theorem int_euclidean_constructive_probe :
    (∀ a b : _root_.Int, b * (a / b) + a % b = a) ∧
      (∀ a : _root_.Int, ∀ {b : _root_.Int}, b ≠ 0 -> 0 ≤ a % b) ∧
      (∀ a : _root_.Int, ∀ {b : _root_.Int}, b ≠ 0 -> a % b < (b.natAbs : _root_.Int)) := by
  exact
    ⟨_root_.Int.mul_ediv_add_emod,
      _root_.Int.emod_nonneg,
      _root_.Int.emod_lt⟩

end BedcMathlibBridge.Export.IntProbe
