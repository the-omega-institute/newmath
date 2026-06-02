import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealCandidateMediatedSNHandoff
    {T F N K X H C P L typedFalse candidateRead normalFrontier sealRead handoffRead namedRead :
      BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory L →
                      Cont T F typedFalse →
                        Cont typedFalse N candidateRead →
                          Cont candidateRead K normalFrontier →
                            Cont normalFrontier X sealRead →
                              Cont H C handoffRead →
                                Cont handoffRead P namedRead →
                                  hsame namedRead L →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row T ∨ hsame row F ∨ hsame row N ∨
                                            hsame row K ∨ hsame row X ∨
                                              hsame row typedFalse ∨
                                                hsame row candidateRead ∨
                                                  hsame row normalFrontier ∨
                                                    hsame row sealRead ∨
                                                      hsame row handoffRead ∨
                                                        hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ hsame namedRead L)
                                        hsame ∧
                                      UnaryHistory typedFalse ∧
                                        UnaryHistory candidateRead ∧
                                          UnaryHistory normalFrontier ∧
                                            UnaryHistory sealRead ∧
                                              UnaryHistory handoffRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryT unaryF unaryN unaryK unaryX unaryH unaryC unaryP _unaryL
  intro typedFalseRoute candidateRoute normalRoute sealRoute handoffRoute namedRoute sameNamed
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed unaryT unaryF typedFalseRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed typedFalseUnary unaryN candidateRoute
  have normalUnary : UnaryHistory normalFrontier :=
    unary_cont_closed candidateUnary unaryK normalRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed normalUnary unaryX sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed unaryH unaryC handoffRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed handoffUnary unaryP namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row typedFalse ∨ hsame row candidateRead ∨
                hsame row normalFrontier ∨ hsame row sealRead ∨ hsame row handoffRead ∨
                  hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ hsame namedRead L)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sameNamed⟩
  }
  exact
    ⟨cert, typedFalseUnary, candidateUnary, normalUnary, sealUnary, handoffUnary,
      namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
