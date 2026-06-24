import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MonotoneBarModulusUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MonotoneBarModulusNonescape
    {T B D W R E H C P N barDepth modulusRead windowRead realRead terminalRead : BHist} :
    Cont T B barDepth ->
      Cont barDepth D modulusRead ->
        Cont modulusRead W windowRead ->
          Cont windowRead R realRead ->
            Cont realRead E terminalRead ->
              UnaryHistory T ->
                UnaryHistory B ->
                  UnaryHistory D ->
                    UnaryHistory W ->
                      UnaryHistory R ->
                        UnaryHistory E ->
                          SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row T ∨ hsame row B ∨ hsame row D ∨
                                  hsame row W ∨ hsame row R ∨ hsame row E ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row realRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont T B barDepth ∧
                                  Cont barDepth D modulusRead ∧
                                    Cont modulusRead W windowRead ∧
                                      Cont windowRead R realRead)
                              hsame ∧
                            UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro barRoute modulusRoute windowRoute realRoute _terminalRoute tUnary bUnary dUnary wUnary
    rUnary _eUnary
  have barDepthUnary : UnaryHistory barDepth :=
    unary_cont_closed tUnary bUnary barRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed barDepthUnary dUnary modulusRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusReadUnary wUnary windowRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed windowReadUnary rUnary realRoute
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row B ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T B barDepth ∧ Cont barDepth D modulusRead ∧
              Cont modulusRead W windowRead ∧ Cont windowRead R realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, barRoute, modulusRoute, windowRoute, realRoute⟩
  }
  exact ⟨cert, realReadUnary⟩

end BEDC.Derived.MonotoneBarModulusUp.TasteGate
