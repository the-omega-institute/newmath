import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization
import BEDC.Derived.UniformCompletionFunctorUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorL10StatusProductNoncollapse [AskSetup] [PackageSetup]
    {U F E R W D S H C P N dyadicRead streamRead regseqRead realRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    uniformCompletionFunctorFields (UniformCompletionFunctorUp.mk U F E R W D S H C P N) =
        [U, F, E, R, W, D, S, H, C, P, N] →
      UnaryHistory D →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory N →
              UnaryHistory H →
                UnaryHistory C →
                  Cont D W dyadicRead →
                    Cont dyadicRead R streamRead →
                      Cont streamRead N regseqRead →
                        Cont R N realRead →
                          Cont H C replayRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      (hsame row dyadicRead ∨ hsame row streamRead ∨
                                          hsame row regseqRead ∨ hsame row realRead) ∧
                                        UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row D ∨ hsame row W ∨ hsame row R ∨
                                        hsame row N ∨ hsame row dyadicRead ∨
                                          hsame row streamRead ∨ hsame row regseqRead ∨
                                            hsame row realRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont D W dyadicRead ∧
                                        Cont dyadicRead R streamRead ∧
                                          Cont streamRead N regseqRead ∧
                                            Cont R N realRead ∧ Cont H C replayRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                                    UnaryHistory regseqRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro fields dUnary wUnary rUnary nUnary hUnary cUnary dyadicRoute streamRoute
    regseqRoute realRoute replayRoute provenancePkg namePkg
  have _acceptedFields :
      uniformCompletionFunctorFields (UniformCompletionFunctorUp.mk U F E R W D S H C P N) =
        [U, F, E, R, W, D, S, H, C, P, N] := fields
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed dUnary wUnary dyadicRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary rUnary streamRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary nUnary regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary nUnary realRoute
  have _replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have sourceAtDyadic :
      (fun row : BHist =>
          (hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
              hsame row realRead) ∧
            UnaryHistory row) dyadicRead := by
    exact ⟨Or.inl (hsame_refl dyadicRead), dyadicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
                hsame row realRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row N ∨
              hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W dyadicRead ∧ Cont dyadicRead R streamRead ∧
              Cont streamRead N regseqRead ∧ Cont R N realRead ∧ Cont H C replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadicRead sourceAtDyadic
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
        intro row other sameRows source
        have sourceSame :
            hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
              hsame row realRead := source.left
        have transported :
            hsame other dyadicRead ∨ hsame other streamRead ∨ hsame other regseqRead ∨
              hsame other realRead := by
          cases sourceSame with
          | inl sameDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
          | inr rest =>
              cases rest with
              | inl sameStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
              | inr rest =>
                  cases rest with
                  | inl sameRegseq =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRegseq)))
                  | inr sameReal =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReal)))
        exact ⟨transported, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl sameDyadic =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDyadic))))
      | inr rest =>
          cases rest with
          | inl sameStream =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream)))))
          | inr rest =>
              cases rest with
              | inl sameRegseq =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl sameRegseq))))))
              | inr sameReal =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sameReal))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, streamRoute, regseqRoute, realRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, regseqUnary, realUnary⟩

end BEDC.Derived.UniformCompletionFunctorUp
