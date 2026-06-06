import BEDC.Derived.WitnessedDescentLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.WitnessedDescentLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem WitnessedDescentLedgerSiblingBoundary (L : WitnessedDescentLedgerUp) :
    ∃ source bridge descentRequest witness transport continuation provenance name : BHist,
      L = WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport
          continuation provenance name ∧
        Cont source bridge (append source bridge) ∧
        Cont descentRequest witness (append descentRequest witness) ∧
        hsame source source ∧
        hsame bridge bridge ∧
        hsame descentRequest descentRequest ∧
        hsame witness witness := by
  -- BEDC touchpoint anchor: BHist hsame Cont append
  cases L with
  | mk source bridge descentRequest witness transport continuation provenance name =>
      exact
        ⟨source, bridge, descentRequest, witness, transport, continuation, provenance, name,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.WitnessedDescentLedgerUp
