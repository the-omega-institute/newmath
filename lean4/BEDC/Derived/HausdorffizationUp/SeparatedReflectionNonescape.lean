import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationSeparatedReflectionNonescape
    {P S M C W R E T K G N boundaryRead completionRead nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N ->
      Cont P S boundaryRead ->
        Cont boundaryRead M completionRead ->
          Cont G N nameRead ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row boundaryRead ∨ hsame row completionRead ∨ hsame row nameRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
                    hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                      hsame row N ∨ hsame row boundaryRead ∨ hsame row completionRead ∨
                        hsame row nameRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                    Cont P S boundaryRead ∧ Cont boundaryRead M completionRead ∧
                      Cont G N nameRead)
                hsame ∧
              UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, _cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryUnary mUnary completionRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundaryRead ∨ hsame row completionRead ∨ hsame row nameRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row boundaryRead ∨ hsame row completionRead ∨
                  hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont boundaryRead M completionRead ∧ Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead
        ⟨Or.inr (Or.inr (hsame_refl nameRead)), nameUnary⟩
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
        constructor
        · cases source.left with
          | inl sameBoundary =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary)
          | inr tail =>
              cases tail with
              | inl sameCompletion =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion))
              | inr sameName =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameName))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBoundary =>
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
                                (Or.inr (Or.inl sameBoundary)))))))))))
      | inr tail =>
          cases tail with
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
                                    (Or.inr
                                      (Or.inr (Or.inl sameCompletion))))))))))))
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
                                      (Or.inr (Or.inr sameName))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierOriginal, boundaryRoute, completionRoute, nameRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, nameUnary⟩

end BEDC.Derived.HausdorffizationUp
