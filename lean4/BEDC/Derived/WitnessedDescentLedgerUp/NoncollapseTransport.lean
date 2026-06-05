import BEDC.Derived.WitnessedDescentLedgerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.WitnessedDescentLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem WitnessedDescentLedgerNoncollapseTransport (L : WitnessedDescentLedgerUp) :
    ∃ source bridge descentRequest witness transport continuation provenance name : BHist,
      L = WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport
          continuation provenance name ∧
        (hsame (BHist.e0 source) (BHist.e1 bridge) → False) ∧
        (hsame (BHist.e0 descentRequest) (BHist.e1 witness) → False) ∧
        Cont source bridge (append source bridge) ∧
        Cont descentRequest witness (append descentRequest witness) := by
  -- BEDC touchpoint anchor: BHist hsame Cont append
  cases L with
  | mk source bridge descentRequest witness transport continuation provenance name =>
      exact
        ⟨source, bridge, descentRequest, witness, transport, continuation, provenance, name,
          rfl,
          fun sameSourceBridge => not_hsame_e0_e1 sameSourceBridge,
          fun sameRequestWitness => not_hsame_e0_e1 sameRequestWitness,
          rfl, rfl⟩

end BEDC.Derived.WitnessedDescentLedgerUp
