import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationPublicExport
    {P S M C W R E T K G N sourceRead separatedRead completionRead replayRead publicRead :
      BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S sourceRead →
        Cont sourceRead M separatedRead →
          Cont separatedRead C completionRead →
            Cont completionRead K replayRead →
              Cont replayRead N publicRead →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                        hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                          hsame row K ∨ hsame row G ∨ hsame row N ∨
                            hsame row sourceRead ∨ hsame row separatedRead ∨
                              hsame row completionRead ∨ hsame row replayRead ∨
                                hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                        Cont P S sourceRead ∧ Cont sourceRead M separatedRead ∧
                          Cont separatedRead C completionRead ∧
                            Cont completionRead K replayRead ∧
                              Cont replayRead N publicRead)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory separatedRead ∧
                    UnaryHistory completionRead ∧ UnaryHistory replayRead ∧
                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: HausdorffizationCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData sourceRoute separatedRoute completionRoute replayRoute publicRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    kUnary, _gUnary, nUnary, _sourceKernelRoute, _handoffRoute⟩ := carrierData
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed pUnary sUnary sourceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed sourceUnary mUnary separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary cUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary kUnary replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row separatedRead ∨
                  hsame row completionRead ∨ hsame row replayRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S sourceRead ∧ Cont sourceRead M separatedRead ∧
                Cont separatedRead C completionRead ∧ Cont completionRead K replayRead ∧
                  Cont replayRead N publicRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierOriginal, sourceRoute, separatedRoute, completionRoute,
          replayRoute, publicRoute⟩
  }
  exact ⟨cert, sourceUnary, separatedUnary, completionUnary, replayUnary, publicUnary⟩

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
