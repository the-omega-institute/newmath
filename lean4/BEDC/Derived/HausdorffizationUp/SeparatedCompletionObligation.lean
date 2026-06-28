import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_separated_completion_obligation
    {P S M C W R E T K G N boundaryRead completionRead windowRead sealRead
      nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont boundaryRead M completionRead →
          Cont completionRead W windowRead →
            Cont windowRead E sealRead →
              Cont G N nameRead →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row completionRead ∨ hsame row sealRead ∨
                          hsame row nameRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                        hsame row W ∨ hsame row E ∨ hsame row G ∨ hsame row N ∨
                          hsame row completionRead ∨ hsame row sealRead ∨
                            hsame row nameRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                        Cont P S boundaryRead ∧ Cont boundaryRead M completionRead ∧
                          Cont completionRead W windowRead ∧ Cont windowRead E sealRead ∧
                            Cont G N nameRead)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute windowRoute sealRoute nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, _cUnary, wUnary, _rUnary, eUnary, _tUnary,
    _kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryUnary mUnary completionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completionRead ∨ hsame row sealRead ∨ hsame row nameRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row E ∨ hsame row G ∨ hsame row N ∨
                hsame row completionRead ∨ hsame row sealRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont boundaryRead M completionRead ∧
                Cont completionRead W windowRead ∧ Cont windowRead E sealRead ∧
                  Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨Or.inr (Or.inl (hsame_refl sealRead)), sealUnary⟩
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
          | inl sameCompletion =>
              exact Or.inl (lift sameCompletion)
          | inr rest =>
              cases rest with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (lift sameSeal))
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
                        (Or.inr (Or.inr (Or.inl sameCompletion))))))))
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inl sameSeal)))))))))
          | inr sameName =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr sameName)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, windowRoute,
          sealRoute, nameRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, windowUnary, sealUnary, nameUnary⟩

end BEDC.Derived.HausdorffizationUp
