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

private theorem int_pos_of_nat_succ (n : Nat) :
    (0 : _root_.Int) < (Nat.succ n : _root_.Int) := by
  exact _root_.Int.natCast_pos.mpr (Nat.succ_pos n)

private theorem int_emod_lt_natAbs_constructive
    (a : _root_.Int) {b : _root_.Int} (hb : b ≠ 0) :
    a % b < (b.natAbs : _root_.Int) := by
  cases b with
  | ofNat n =>
      cases n with
      | zero =>
          contradiction
      | succ n =>
          change a % (_root_.Int.ofNat (Nat.succ n)) < _root_.Int.ofNat (Nat.succ n)
          exact _root_.Int.emod_lt_of_pos a (int_pos_of_nat_succ n)
  | negSucc n =>
      rw [_root_.Int.negSucc_eq]
      rw [_root_.Int.emod_neg]
      change a % (_root_.Int.ofNat (Nat.succ n)) < _root_.Int.ofNat (Nat.succ n)
      exact _root_.Int.emod_lt_of_pos a (int_pos_of_nat_succ n)

theorem int_euclidean_constructive_probe :
    (∀ a b : _root_.Int, b * (a / b) + a % b = a) ∧
      (∀ a : _root_.Int, ∀ {b : _root_.Int}, b ≠ 0 -> 0 ≤ a % b) ∧
      (∀ a : _root_.Int, ∀ {b : _root_.Int}, b ≠ 0 -> a % b < (b.natAbs : _root_.Int)) := by
  exact
    ⟨_root_.Int.mul_ediv_add_emod,
      _root_.Int.emod_nonneg,
      int_emod_lt_natAbs_constructive⟩

theorem int_ordered_ring_constructive_probe :
    (∀ a b : _root_.Int, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b) ∧
      (∀ a b c : _root_.Int, a ≤ b -> a + c ≤ b + c) := by
  exact
    ⟨fun _ _ ha hb => _root_.Int.mul_nonneg ha hb,
      fun _ _ _ h => _root_.Int.add_le_add_right h _⟩

theorem int_strict_ordered_ring_constructive_probe :
    (∀ a b : _root_.Int, 0 < a -> 0 < b -> 0 < a * b) ∧
      (∀ a b c : _root_.Int, a ≤ b -> a + c ≤ b + c) := by
  exact
    ⟨fun _ _ ha hb => _root_.Int.mul_pos ha hb,
      fun _ _ _ h => _root_.Int.add_le_add_right h _⟩

end BedcMathlibBridge.Export.IntProbe
