import BEDC.Derived.PinGroupUp

namespace BEDC.Derived.PinGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PinGroupReflectionParityLedgerSurface_root_scoped_obligation_package
    {spin reflection product endpoint ledger carried action actionOut provenance spinLedger
      spinCarried spinReflected : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      UnaryHistory spin ->
        Cont spin spinLedger spinCarried ->
          Cont BHist.Empty spinCarried spinReflected ->
            Cont reflection carried action ->
              Cont action provenance actionOut ->
                hsame provenance BHist.Empty ->
                  (PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger
                      carried ∧
                    PinGroupReflectionParityLedgerSurface spin BHist.Empty BHist.Empty spin
                      spinLedger spinCarried) ∧
                    hsame spinCarried (append spin spinLedger) ∧
                      hsame spinReflected spinCarried ∧
                        hsame actionOut (append reflection carried) ∧
                          hsame carried (append endpoint ledger) ∧
                            (hsame endpoint spin ∨ hsame endpoint product) := by
  intro surface spinUnary spinLedgerRow spinReflectedRow actionRow actionOutRow provenanceEmpty
  have spinReadback :=
    PinGroupSpinSubrowClassifier_readback spinUnary spinLedgerRow spinReflectedRow
  have actionRows :=
    PinGroupReflectionParityLedgerSurface_clifford_action_ledger_obligation surface actionRow
      actionOutRow provenanceEmpty
  exact
    And.intro (And.intro surface spinReadback.left)
      (And.intro spinReadback.right.left
        (And.intro spinReadback.right.right
          (And.intro actionRows.right.right.left
            (And.intro actionRows.right.left actionRows.right.right.right))))

end BEDC.Derived.PinGroupUp
