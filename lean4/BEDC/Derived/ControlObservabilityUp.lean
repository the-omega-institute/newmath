import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ControlObservabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def ControlObservabilityFiniteTraceLedger
    (state transition output observationMatrix traceLedger provenance : BHist) : Prop :=
  Cont state transition observationMatrix ∧ Cont observationMatrix output traceLedger ∧
    hsame provenance BHist.Empty

theorem ControlObservabilityFiniteTraceLedger_readback
    {state transition output observationMatrix traceLedger provenance : BHist} :
    ControlObservabilityFiniteTraceLedger state transition output observationMatrix traceLedger
      provenance ->
      hsame observationMatrix (append state transition) ∧
        hsame traceLedger (append observationMatrix output) ∧ hsame provenance BHist.Empty ∧
          SemanticNameCert (fun row : BHist => row = traceLedger)
            (fun row : BHist => row = traceLedger)
            (fun row : BHist => row = traceLedger) hsame := by
  intro ledger
  cases ledger with
  | intro observationRow ledgerRest =>
      cases ledgerRest with
      | intro traceRow provenanceEmpty =>
          constructor
          · exact observationRow
          · constructor
            · exact traceRow
            · constructor
              · exact provenanceEmpty
              · exact {
                  core := {
                    carrier_inhabited := ⟨traceLedger, rfl⟩
                    equiv_refl := by
                      intro row _source
                      exact hsame_refl row
                    equiv_symm := by
                      intro _row _row' same
                      exact hsame_symm same
                    equiv_trans := by
                      intro _row _row' _row'' sameLeft sameRight
                      exact hsame_trans sameLeft sameRight
                    carrier_respects_equiv := by
                      intro _row _row' same source
                      exact (hsame_symm same).trans source
                  }
                  pattern_sound := by
                    intro _row source
                    exact source
                  ledger_sound := by
                    intro _row source
                    exact source
                }

end BEDC.Derived.ControlObservabilityUp
