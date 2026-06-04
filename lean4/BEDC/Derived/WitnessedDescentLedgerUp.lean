import BEDC.Derived.WitnessedDescentLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.WitnessedDescentLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem WitnessedDescentLedgerNamecertObligations (L : WitnessedDescentLedgerUp) :
    ∃ source bridge descentRequest witness transport continuation provenance name : BHist,
      L = WitnessedDescentLedgerUp.mk source bridge descentRequest witness transport
        continuation provenance name ∧
      hsame transport transport ∧
      Cont source bridge (append source bridge) ∧
      NameCert (fun h : BHist => hsame h name) hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont NameCert
  cases L with
  | mk source bridge descentRequest witness transport continuation provenance name =>
      exact
        ⟨source, bridge, descentRequest, witness, transport, continuation, provenance, name,
          rfl, rfl, rfl,
          { carrier_inhabited := Exists.intro name rfl
            equiv_refl := by
              intro _h _carrier
              rfl
            equiv_symm := by
              intro _h _k hk
              exact hk.symm
            equiv_trans := by
              intro _h _k _r hk kr
              exact hk.trans kr
            carrier_respects_equiv := by
              intro _h _k hk carrier
              cases hk
              exact carrier }⟩

end BEDC.Derived.WitnessedDescentLedgerUp
