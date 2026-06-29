import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_separated_real_completion_scope
    {P S M C W R E T K G N boundaryRead completionRead realRead separatedRead
      scopeRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont W R realRead →
            Cont completionRead E separatedRead →
              Cont separatedRead N scopeRead →
                SemanticNameCert
                    (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                        hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                          hsame row K ∨ hsame row G ∨ hsame row N ∨
                            hsame row boundaryRead ∨ hsame row completionRead ∨
                              hsame row realRead ∨ hsame row separatedRead ∨
                                hsame row scopeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                        Cont P S boundaryRead ∧ Cont M C completionRead ∧
                          Cont W R realRead ∧ Cont completionRead E separatedRead ∧
                            Cont separatedRead N scopeRead)
                    hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory realRead ∧ UnaryHistory separatedRead ∧
                    UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute realRoute separatedRoute scopeRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, mUnary, cUnary, wUnary, rUnary, eUnary, _tUnary,
    _kUnary, _gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed wUnary rUnary realRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionUnary eUnary separatedRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed separatedUnary nUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row boundaryRead ∨ hsame row completionRead ∨
                  hsame row realRead ∨ hsame row separatedRead ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont P S boundaryRead ∧ Cont M C completionRead ∧ Cont W R realRead ∧
                Cont completionRead E separatedRead ∧ Cont separatedRead N scopeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
                                    (Or.inr sourceRow.left))))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, boundaryRoute, completionRoute, realRoute,
          separatedRoute, scopeRoute⟩
  }
  exact
    ⟨cert, boundaryUnary, completionUnary, realUnary, separatedUnary, scopeUnary⟩

end HausdorffizationUp

end BEDC.Derived
