import BEDC.Derived.PinGroupUp

namespace BEDC.Derived.PinGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PinGroupReflectionParityLedgerSurface_clifford_conjugation_ledger
    {spin reflection product endpoint ledger carried action actionOut provenance reflected : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      Cont reflection carried action ->
        Cont action provenance actionOut ->
          hsame provenance BHist.Empty ->
            Cont carried reflection reflected ->
              ((hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
                  (hsame carried (append product ledger) ∧ Cont spin reflection product ∧
                    UnaryHistory reflection)) ∧
                hsame carried (append endpoint ledger) ∧
                  hsame actionOut (append reflection carried) ∧
                    hsame reflected (append carried reflection) ∧
                      (hsame endpoint spin ∨ hsame endpoint product) := by
  intro surface actionRow actionProvenance provenanceEmpty reflectedRow
  have actionRows :=
    PinGroupReflectionParityLedgerSurface_clifford_action_ledger_obligation surface actionRow
      actionProvenance provenanceEmpty
  exact And.intro actionRows.left
    (And.intro actionRows.right.left
      (And.intro actionRows.right.right.left
        (And.intro reflectedRow actionRows.right.right.right)))

end BEDC.Derived.PinGroupUp
