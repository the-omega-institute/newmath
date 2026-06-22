import BEDC.Derived.MarkovPrincipleBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MarkovPrincipleBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MarkovPrincipleBoundaryIshiharaSpeckerRoute
    {inspection specker schedule readback dyadic realSeal witness transport replay provenance
      localName branchRead witnessRead : BHist} :
    Cont inspection schedule branchRead →
      Cont branchRead dyadic witnessRead →
        UnaryHistory inspection →
          UnaryHistory specker →
            UnaryHistory schedule →
              UnaryHistory readback →
                UnaryHistory dyadic →
                  UnaryHistory realSeal →
                    UnaryHistory witness →
                      UnaryHistory transport →
                        UnaryHistory replay →
                          UnaryHistory provenance →
                            UnaryHistory localName →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row witnessRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row inspection ∨ hsame row specker ∨
                                      hsame row schedule ∨ hsame row readback ∨
                                        hsame row dyadic ∨ hsame row realSeal ∨
                                          hsame row witness ∨ hsame row witnessRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont inspection schedule branchRead ∧
                                      Cont branchRead dyadic witnessRead)
                                  hsame ∧
                                UnaryHistory branchRead ∧ UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: MarkovPrincipleBoundaryUp BHist Cont SemanticNameCert hsame UnaryHistory
  intro branchRoute witnessRoute inspectionUnary _speckerUnary scheduleUnary _readbackUnary
    dyadicUnary _realSealUnary _witnessUnary _transportUnary _replayUnary _provenanceUnary
    _localNameUnary
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed inspectionUnary scheduleUnary branchRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed branchUnary dyadicUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row inspection ∨ hsame row specker ∨ hsame row schedule ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row realSeal ∨
                hsame row witness ∨ hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont inspection schedule branchRead ∧
              Cont branchRead dyadic witnessRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead
        ⟨hsame_refl witnessRead, witnessReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, branchRoute, witnessRoute⟩
  }
  exact ⟨cert, branchUnary, witnessReadUnary⟩

end BEDC.Derived.MarkovPrincipleBoundaryUp
