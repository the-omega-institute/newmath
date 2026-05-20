import BEDC.Derived.TowerEquivalenceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.TowerEquivalenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TowerEquivalenceRefinementSeparation
    {tower tower' approx approx' physical physical' openFit openFit' objectivity ledger
      ledger' descent descent' endpoint transport provenance name refinement : BHist} :
    Cont endpoint ledger refinement →
      (ledger ≠ ledger' ∨ descent ≠ descent') →
        towerEquivalenceFields
            (TowerEquivalenceUp.mk tower tower' approx approx' physical physical' openFit
              openFit' objectivity ledger descent endpoint transport provenance name) ≠
          towerEquivalenceFields
            (TowerEquivalenceUp.mk tower tower' approx approx' physical physical' openFit
              openFit' objectivity ledger' descent' endpoint transport provenance name) := by
  -- BEDC touchpoint anchor: BHist Cont
  intro _refinementRoute separated sameFields
  cases separated with
  | inl ledgerSeparated =>
      injection sameFields with _towerEq tail1
      injection tail1 with _towerPrimeEq tail2
      injection tail2 with _approxEq tail3
      injection tail3 with _approxPrimeEq tail4
      injection tail4 with _physicalEq tail5
      injection tail5 with _physicalPrimeEq tail6
      injection tail6 with _openFitEq tail7
      injection tail7 with _openFitPrimeEq tail8
      injection tail8 with _objectivityEq tail9
      injection tail9 with ledgerEq _tail10
      exact ledgerSeparated ledgerEq
  | inr descentSeparated =>
      injection sameFields with _towerEq tail1
      injection tail1 with _towerPrimeEq tail2
      injection tail2 with _approxEq tail3
      injection tail3 with _approxPrimeEq tail4
      injection tail4 with _physicalEq tail5
      injection tail5 with _physicalPrimeEq tail6
      injection tail6 with _openFitEq tail7
      injection tail7 with _openFitPrimeEq tail8
      injection tail8 with _objectivityEq tail9
      injection tail9 with _ledgerEq tail10
      injection tail10 with descentEq _tail11
      exact descentSeparated descentEq

end BEDC.Derived.TowerEquivalenceUp
