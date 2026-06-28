import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_completion_boundary_exhaustion
    {P S M C W R E T K G N boundaryRead completionRead realRead replayRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont W R realRead →
          Cont M C completionRead →
            Cont completionRead K replayRead →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                        hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                      Cont P S boundaryRead ∧ Cont W R realRead ∧
                        Cont M C completionRead ∧ Cont completionRead K replayRead)
                  hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                UnaryHistory realRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute realRoute completionRoute replayRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, wUnary, rUnary, _eUnary, _tUnary,
    kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed wUnary rUnary realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary kUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont W R realRead ∧ Cont M C completionRead ∧
                Cont completionRead K replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
                          (Or.inr (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, boundaryRoute, realRoute, completionRoute,
          replayRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, realUnary, replayUnary⟩

end HausdorffizationUp

end BEDC.Derived
