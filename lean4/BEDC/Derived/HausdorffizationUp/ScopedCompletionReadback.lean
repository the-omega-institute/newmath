import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_scoped_completion_readback
    {P S M C W R E T K G N boundaryRead completionRead scopedRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont completionRead K scopedRead →
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                      hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                    Cont P S boundaryRead ∧ Cont M C completionRead ∧
                      Cont completionRead K scopedRead)
                hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
              UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute scopedRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed completionUnary kUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont M C completionRead ∧
                Cont completionRead K scopedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, scopedRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, scopedUnary⟩

theorem HausdorffizationCarrier_route_readback_bundle
    {P S M C W R E T K G N zeroRead boundaryRead completionRead replayRead
      nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P W zeroRead →
        Cont P S boundaryRead →
          Cont M C completionRead →
            Cont T K replayRead →
              Cont G N nameRead →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row zeroRead ∨ hsame row boundaryRead ∨
                          hsame row completionRead ∨ hsame row replayRead ∨
                            hsame row nameRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                        hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                          hsame row K ∨ hsame row G ∨ hsame row N ∨
                            hsame row zeroRead ∨ hsame row boundaryRead ∨
                              hsame row completionRead ∨ hsame row replayRead ∨
                                hsame row nameRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                        Cont P W zeroRead ∧ Cont P S boundaryRead ∧
                          Cont M C completionRead ∧ Cont T K replayRead ∧
                            Cont G N nameRead)
                    hsame ∧ UnaryHistory zeroRead ∧ UnaryHistory boundaryRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory replayRead ∧
                        UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData zeroRoute boundaryRoute completionRoute replayRoute nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, wUnary, _rUnary, _eUnary, tUnary,
    kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have zeroUnary : UnaryHistory zeroRead := unary_cont_closed pUnary wUnary zeroRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have replayUnary : UnaryHistory replayRead := unary_cont_closed tUnary kUnary replayRoute
  have nameUnary : UnaryHistory nameRead := unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row zeroRead ∨ hsame row boundaryRead ∨ hsame row completionRead ∨
                hsame row replayRead ∨ hsame row nameRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row zeroRead ∨ hsame row boundaryRead ∨
                  hsame row completionRead ∨ hsame row replayRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P W zeroRead ∧ Cont P S boundaryRead ∧ Cont M C completionRead ∧
                Cont T K replayRead ∧ Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro zeroRead ⟨Or.inl (hsame_refl zeroRead), zeroUnary⟩
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
        intro row other sameRows sourceRow
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameZero =>
              exact Or.inl (lift sameZero)
          | inr rest =>
              cases rest with
              | inl sameBoundary =>
                  exact Or.inr (Or.inl (lift sameBoundary))
              | inr rest =>
                  cases rest with
                  | inl sameCompletion =>
                      exact Or.inr (Or.inr (Or.inl (lift sameCompletion)))
                  | inr rest =>
                      cases rest with
                      | inl sameReplay =>
                          exact Or.inr (Or.inr (Or.inr (Or.inl (lift sameReplay))))
                      | inr sameName =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (lift sameName))))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameZero =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          exact Or.inl sameZero
      | inr rest =>
          cases rest with
          | inl sameBoundary =>
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              exact Or.inl sameBoundary
          | inr rest =>
              cases rest with
              | inl sameCompletion =>
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  exact Or.inl sameCompletion
              | inr rest =>
                  cases rest with
                  | inl sameReplay =>
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      exact Or.inl sameReplay
                  | inr sameName =>
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      apply Or.inr
                      exact sameName
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, zeroRoute, boundaryRoute, completionRoute,
          replayRoute, nameRoute⟩
  }
  exact ⟨cert, zeroUnary, boundaryUnary, completionUnary, replayUnary, nameUnary⟩

end BEDC.Derived.HausdorffizationUp
