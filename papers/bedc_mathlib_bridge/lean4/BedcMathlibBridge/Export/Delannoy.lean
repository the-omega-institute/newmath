import BedcMathlibBridge.Constructive.Delannoy

namespace BedcMathlibBridge.Export.Delannoy

open BedcMathlibBridge.Constructive.Delannoy

structure DelannoyClosedFormTermExportWitness where
  readback : Nat -> Nat -> Nat -> Nat
  readback_apply : ∀ m n k : Nat, readback m n k = closedFormTerm m n k
  bedc_apply : ∀ m n k : Nat,
    readback m n k = BEDC.Derived.DelannoyUp.delannoyClosedFormTerm m n k
  nat_choose_apply : ∀ m n k : Nat,
    readback m n k = Nat.choose m k * Nat.choose n k * 2 ^ k

def delannoyClosedFormTermExport : DelannoyClosedFormTermExportWitness where
  readback := closedFormTerm
  readback_apply := by
    intro m n k
    rfl
  bedc_apply := closedFormTerm_apply
  nat_choose_apply := closedFormTerm_eq_nat_choose_term

theorem delannoyClosedFormTerm_eq_nat_choose_term (m n k : Nat) :
    BEDC.Derived.DelannoyUp.delannoyClosedFormTerm m n k =
      Nat.choose m k * Nat.choose n k * 2 ^ k :=
  (BedcMathlibBridge.Constructive.Delannoy.closedFormTerm_apply m n k).symm.trans
    (BedcMathlibBridge.Constructive.Delannoy.closedFormTerm_eq_nat_choose_term m n k)

end BedcMathlibBridge.Export.Delannoy
