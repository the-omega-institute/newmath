import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_metriccompletion_handoff
    {P S M C W R E T K G N completionRead realRead nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont M C completionRead →
        Cont W R realRead →
          Cont G N nameRead →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row completionRead ∨ hsame row realRead ∨ hsame row nameRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                      hsame row K ∨ hsame row G ∨ hsame row N ∨
                        hsame row completionRead ∨ hsame row realRead ∨
                          hsame row nameRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                    Cont M C completionRead ∧ Cont W R realRead ∧ Cont G N nameRead)
                hsame ∧
              UnaryHistory completionRead ∧ UnaryHistory realRead ∧
                UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData completionRoute realRoute nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨_pUnary, _sUnary, mUnary, cUnary, wUnary, rUnary, _eUnary, _tUnary,
    _kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed wUnary rUnary realRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completionRead ∨ hsame row realRead ∨ hsame row nameRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨
                hsame row G ∨ hsame row N ∨ hsame row completionRead ∨
                  hsame row realRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont M C completionRead ∧ Cont W R realRead ∧ Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          ⟨Or.inl (hsame_refl completionRead), completionUnary⟩
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
        have lift : ∀ {target : BHist}, hsame _row target → hsame _other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameCompletion =>
              exact Or.inl (lift sameCompletion)
          | inr rest =>
              cases rest with
              | inl sameReal =>
                  exact Or.inr (Or.inl (lift sameReal))
              | inr sameName =>
                  exact Or.inr (Or.inr (lift sameName))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameCompletion =>
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
                                (Or.inr (Or.inl sameCompletion)))))))))))
      | inr rest =>
          cases rest with
          | inl sameReal =>
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
                                      (Or.inr (Or.inl sameReal))))))))))))
          | inr sameName =>
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
                                        (Or.inr sameName))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, completionRoute, realRoute, nameRoute⟩
  }
  exact ⟨cert, completionUnary, realUnary, nameUnary⟩

theorem HausdorffizationCarrier_complete_metric_limit_uniqueness_route
    {P S M C W R E T K G N boundaryRead completionRead uniquenessRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont completionRead G uniquenessRead →
            SemanticNameCert
                (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                      hsame row K ∨ hsame row G ∨ hsame row N ∨
                        hsame row uniquenessRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                    Cont P S boundaryRead ∧ Cont M C completionRead ∧
                      Cont completionRead G uniquenessRead)
                hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory uniquenessRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute uniquenessRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed completionUnary gUnary uniquenessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row uniquenessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont M C completionRead ∧
                Cont completionRead G uniquenessRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniquenessRead ⟨hsame_refl uniquenessRead, uniquenessUnary⟩
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
      exact ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, uniquenessRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, uniquenessUnary⟩

end HausdorffizationUp

end BEDC.Derived
