import BEDC.Derived.CauchyDifferenceCriterionUp.ZeroDistanceCorrespondence

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionCarrier_regular_tail_stability [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N retainedDiff retainedNull retainedZero retainedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] ->
      UnaryHistory D ->
        UnaryHistory Z ->
          UnaryHistory Q ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  Cont D H retainedDiff ->
                    Cont retainedDiff Z retainedNull ->
                      Cont retainedNull Q retainedZero ->
                        Cont retainedZero C retainedSeal ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row retainedSeal ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row D ∨ hsame row Z ∨ hsame row Q ∨
                                      hsame row E ∨ hsame row H ∨ hsame row C ∨
                                        hsame row retainedSeal)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont D H retainedDiff ∧
                                      Cont retainedDiff Z retainedNull ∧
                                        Cont retainedNull Q retainedZero ∧
                                          Cont retainedZero C retainedSeal ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory retainedDiff ∧
                                  UnaryHistory retainedNull ∧
                                    UnaryHistory retainedZero ∧
                                      UnaryHistory retainedSeal := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields dUnary zUnary qUnary _eUnary hUnary cUnary retainedDiffRoute
    retainedNullRoute retainedZeroRoute retainedSealRoute pPkg nPkg
  have _acceptedFields :
      cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := fields
  have retainedDiffUnary : UnaryHistory retainedDiff :=
    unary_cont_closed dUnary hUnary retainedDiffRoute
  have retainedNullUnary : UnaryHistory retainedNull :=
    unary_cont_closed retainedDiffUnary zUnary retainedNullRoute
  have retainedZeroUnary : UnaryHistory retainedZero :=
    unary_cont_closed retainedNullUnary qUnary retainedZeroRoute
  have retainedSealUnary : UnaryHistory retainedSeal :=
    unary_cont_closed retainedZeroUnary cUnary retainedSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row retainedSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row Z ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row retainedSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D H retainedDiff ∧ Cont retainedDiff Z retainedNull ∧
              Cont retainedNull Q retainedZero ∧ Cont retainedZero C retainedSeal ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro retainedSeal ⟨hsame_refl retainedSeal, retainedSealUnary⟩
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
        ⟨source.right, retainedDiffRoute, retainedNullRoute, retainedZeroRoute,
          retainedSealRoute, pPkg, nPkg⟩
  }
  exact
    ⟨cert, retainedDiffUnary, retainedNullUnary, retainedZeroUnary,
      retainedSealUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
