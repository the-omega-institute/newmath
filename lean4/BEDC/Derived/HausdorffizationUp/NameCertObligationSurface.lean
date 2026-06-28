import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_namecert_obligation_surface
    {P S M C W R E T K G N boundaryRead completionRead readbackRead replayRead
      nameRead surface : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont W R readbackRead →
            Cont T K replayRead →
              Cont G N nameRead →
                Cont boundaryRead completionRead surface →
                  SemanticNameCert
                      (fun row : BHist => hsame row surface ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                          hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                            hsame row K ∨ hsame row G ∨ hsame row N ∨
                              hsame row boundaryRead ∨ hsame row completionRead ∨
                                hsame row readbackRead ∨ hsame row replayRead ∨
                                  hsame row nameRead ∨ hsame row surface)
                      (fun row : BHist =>
                        UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                          Cont P S boundaryRead ∧ Cont M C completionRead ∧
                            Cont W R readbackRead ∧ Cont T K replayRead ∧
                              Cont G N nameRead ∧ Cont boundaryRead completionRead surface)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory replayRead ∧
                        UnaryHistory nameRead ∧ UnaryHistory surface := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute readbackRoute replayRoute nameRoute surfaceRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, wUnary, rUnary, _eUnary, tUnary, kUnary,
    gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed wUnary rUnary readbackRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed tUnary kUnary replayRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed boundaryUnary completionUnary surfaceRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro surface ⟨hsame_refl surface, surfaceUnary⟩
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
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr sourceRow.left)))))))))))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, readbackRoute,
            replayRoute, nameRoute, surfaceRoute⟩
    }
  · exact
      ⟨boundaryUnary, completionUnary, readbackUnary, replayUnary, nameUnary,
        surfaceUnary⟩

end BEDC.Derived.HausdorffizationUp
