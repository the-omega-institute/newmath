import BEDC.Derived.TwinSubstrateAuditCouplingUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TwinSubstrateAuditCouplingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def TwinSubstrateAuditCouplingObligationRowSpec
    (M G R L C H T P N row : BHist) : Prop :=
  hsame row M ∨ hsame row G ∨ hsame row R ∨ hsame row L ∨ hsame row C ∨
    hsame row H ∨ hsame row T ∨ hsame row P ∨ hsame row N

theorem TwinSubstrateAuditCouplingNameCertObligations (M G R L C H T P N : BHist) :
    SemanticNameCert
      (TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N)
      (TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N)
      (TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  let rowSpec := TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N
  have carrierInhabited : ∃ row : BHist, rowSpec row :=
    ⟨M, Or.inl (hsame_refl M)⟩
  have rowSpecTransport :
      ∀ row other : BHist, hsame row other → rowSpec row → rowSpec other := by
    intro row other sameRows source
    cases sameRows
    exact source
  exact {
    core := {
      carrier_inhabited := carrierInhabited
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        exact rowSpecTransport row other sameRows source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.TwinSubstrateAuditCouplingUp
