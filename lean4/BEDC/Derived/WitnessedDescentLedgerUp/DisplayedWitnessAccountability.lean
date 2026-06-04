import BEDC.Derived.WitnessedDescentLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.WitnessedDescentLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem WitnessedDescentLedgerDisplayedWitnessAccountability
    (L : WitnessedDescentLedgerUp) :
    ∃ source bridge descentRequest witness transport continuation provenance name : BHist,
      L = WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport
        continuation provenance name ∧
      hsame witness witness ∧
      Cont descentRequest witness (append descentRequest witness) ∧
      NameCert (fun h : BHist => hsame h witness) hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont NameCert
  cases L with
  | mk source bridge descentRequest witness transport continuation provenance name =>
      have semanticCert :
          SemanticNameCert
            (fun h : BHist => hsame h witness)
            (fun h : BHist => hsame h witness)
            (fun h : BHist => hsame h witness)
            hsame := {
        core := {
          carrier_inhabited := Exists.intro witness (hsame_refl witness)
          equiv_refl := by
            intro row _carrier
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other sameRows carrier
            exact hsame_trans (hsame_symm sameRows) carrier
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
      exact
        ⟨source, bridge, descentRequest, witness, transport, continuation, provenance, name,
          rfl, hsame_refl witness, rfl, semanticCert.core⟩

end BEDC.Derived.WitnessedDescentLedgerUp
