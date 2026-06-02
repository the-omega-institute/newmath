import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMetaCICDischargeFrontier
    {T F N K X _H C P L typedFalse normalTheorem boundaryRead metacicRead : BHist} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory C →
                UnaryHistory P →
                  UnaryHistory L →
                    Cont T F typedFalse →
                      Cont N K normalTheorem →
                        Cont normalTheorem X boundaryRead →
                          Cont boundaryRead C metacicRead →
                            SemanticNameCert
                                (fun row : BHist => hsame row metacicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row N ∨
                                    hsame row K ∨ hsame row X ∨ hsame row boundaryRead ∨
                                      hsame row metacicRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont normalTheorem X boundaryRead ∧
                                    Cont boundaryRead C metacicRead)
                                hsame ∧
                              UnaryHistory boundaryRead ∧ UnaryHistory metacicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryT unaryF unaryN unaryK unaryX unaryC _unaryP _unaryL
  intro typedFalseRoute normalRoute boundaryRoute metacicRoute
  have _typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed unaryT unaryF typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed unaryN unaryK normalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed normalTheoremUnary unaryX boundaryRoute
  have metacicUnary : UnaryHistory metacicRead :=
    unary_cont_closed boundaryUnary unaryC metacicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metacicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row boundaryRead ∨ hsame row metacicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont normalTheorem X boundaryRead ∧
              Cont boundaryRead C metacicRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro metacicRead ⟨hsame_refl metacicRead, metacicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, metacicRoute⟩
  }
  exact ⟨cert, boundaryUnary, metacicUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
