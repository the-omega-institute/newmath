import BedcMathlibBridge.Constructive.Apery

namespace BedcMathlibBridge.Export.Apery

open BedcMathlibBridge.Constructive.Apery

structure AperyExportWitness where
  readbackA : Nat -> Nat
  readbackB : Nat -> Nat
  readbackA_apply : forall n : Nat, readbackA n = BedcMathlibBridge.Constructive.Apery.readbackA n
  readbackB_apply : forall n : Nat, readbackB n = BedcMathlibBridge.Constructive.Apery.readbackB n
  bedcA_apply : forall n : Nat, readbackA n = BEDC.Derived.AperyUp.aperyA n
  bedcB_apply : forall n : Nat, readbackB n = BEDC.Derived.AperyUp.aperyB n
  a_nat_choose_sum : forall n : Nat,
    readbackA n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) *
            (Nat.choose (n + k) k * Nat.choose (n + k) k))
  b_nat_choose_sum : forall n : Nat,
    readbackB n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) * Nat.choose (n + k) k)

def aperyExport : AperyExportWitness where
  readbackA := readbackA
  readbackB := readbackB
  readbackA_apply := by
    intro n
    rfl
  readbackB_apply := by
    intro n
    rfl
  bedcA_apply := readbackA_apply
  bedcB_apply := readbackB_apply
  a_nat_choose_sum := readbackA_eq_nat_choose_sum
  b_nat_choose_sum := readbackB_eq_nat_choose_sum

theorem aperyA_eq_nat_choose_sum (n : Nat) :
    BEDC.Derived.AperyUp.aperyA n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) *
            (Nat.choose (n + k) k * Nat.choose (n + k) k)) :=
  (BedcMathlibBridge.Constructive.Apery.readbackA_apply n).symm.trans
    (BedcMathlibBridge.Constructive.Apery.readbackA_eq_nat_choose_sum n)

theorem aperyB_eq_nat_choose_sum (n : Nat) :
    BEDC.Derived.AperyUp.aperyB n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) * Nat.choose (n + k) k) :=
  (BedcMathlibBridge.Constructive.Apery.readbackB_apply n).symm.trans
    (BedcMathlibBridge.Constructive.Apery.readbackB_eq_nat_choose_sum n)

end BedcMathlibBridge.Export.Apery
