import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_public_export
    {P S M C W R E T K G N boundaryRead completionRead replayRead nameRead
      publicRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont T K replayRead →
            Cont G N nameRead →
              Cont completionRead N publicRead →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                        hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                          hsame row K ∨ hsame row G ∨ hsame row N ∨
                            hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                        Cont P S boundaryRead ∧ Cont M C completionRead ∧
                          Cont T K replayRead ∧ Cont G N nameRead ∧
                            Cont completionRead N publicRead)
                    hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory replayRead ∧ UnaryHistory nameRead ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute replayRoute nameRoute publicRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, tUnary,
    kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary kUnary replayRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont M C completionRead ∧
                Cont T K replayRead ∧ Cont G N nameRead ∧
                  Cont completionRead N publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, replayRoute,
          nameRoute, publicRoute⟩
  }
  exact
    ⟨cert, boundaryUnary, completionUnary, replayUnary, nameUnary, publicUnary⟩

end HausdorffizationUp

end BEDC.Derived
