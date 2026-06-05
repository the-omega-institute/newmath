import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricDisplayRoute [AskSetup] [PackageSetup]
    {X S R M L D H C P N sourceRead rationalRead modulusRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory R ->
            UnaryHistory M ->
              UnaryHistory L ->
                Cont X S sourceRead ->
                  Cont sourceRead R rationalRead ->
                    Cont rationalRead M modulusRead ->
                      Cont modulusRead L limitRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row S ∨ hsame row R ∨
                                    hsame row M ∨ hsame row L ∨ hsame row D ∨
                                      hsame row limitRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X S sourceRead ∧
                                    Cont sourceRead R rationalRead ∧
                                      Cont rationalRead M modulusRead ∧
                                        Cont modulusRead L limitRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary rUnary mUnary lUnary sourceRoute rationalRoute modulusRoute
    limitRoute provenancePkg namePkg
  cases fieldRows
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary sUnary sourceRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed sourceUnary rUnary rationalRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed rationalUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro limitRead ⟨hsame_refl limitRead, limitUnary⟩
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
        exact
          ⟨source.right, sourceRoute, rationalRoute, modulusRoute, limitRoute,
            provenancePkg, namePkg⟩
    }
  · exact limitUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
