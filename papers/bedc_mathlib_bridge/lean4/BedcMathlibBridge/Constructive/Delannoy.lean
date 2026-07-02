import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.DelannoyUp

namespace BedcMathlibBridge.Constructive.Delannoy

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def closedFormTerm (m n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.DelannoyUp.delannoyClosedFormTerm m n k

theorem closedFormTerm_apply (m n k : Nat) :
    closedFormTerm m n k =
      BEDC.Derived.DelannoyUp.delannoyClosedFormTerm m n k := by
  rfl

private theorem binomialIdentitiesC_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

theorem closedFormTerm_eq_nat_choose_term (m n k : Nat) :
    closedFormTerm m n k = Nat.choose m k * Nat.choose n k * 2 ^ k := by
  unfold closedFormTerm BEDC.Derived.DelannoyUp.delannoyClosedFormTerm
  unfold BEDC.Derived.DelannoyUp.C
  rw [binomialIdentitiesC_eq_nat_choose m k]
  rw [binomialIdentitiesC_eq_nat_choose n k]

end BedcMathlibBridge.Constructive.Delannoy
