import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_budgeted_common_refinement [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert
      observationBudget budgetWindow budgetReadback budgetSeal commonRefinement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg ->
      UnaryHistory observationBudget ->
        Cont modulus observationBudget budgetWindow ->
          Cont budgetWindow readback budgetReadback ->
            Cont budgetReadback sealRow budgetSeal ->
              Cont budgetSeal provenance commonRefinement ->
                PkgSig bundle commonRefinement pkg ->
                  UnaryHistory budgetWindow ∧ UnaryHistory budgetReadback ∧
                    UnaryHistory budgetSeal ∧ UnaryHistory commonRefinement ∧
                      Cont modulus observationBudget budgetWindow ∧
                        Cont budgetWindow readback budgetReadback ∧
                          Cont budgetReadback sealRow budgetSeal ∧
                            Cont budgetSeal provenance commonRefinement ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle commonRefinement pkg := by
  intro carrier observationBudgetUnary modulusBudgetWindow budgetWindowReadback
  intro budgetReadbackSeal budgetSealProvenance commonRefinementPkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, provenanceUnary,
    familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalProvenance, provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusDiagonal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed modulusUnary observationBudgetUnary modulusBudgetWindow
  have budgetReadbackUnary : UnaryHistory budgetReadback :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowReadback
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadbackUnary sealUnary budgetReadbackSeal
  have commonRefinementUnary : UnaryHistory commonRefinement :=
    unary_cont_closed budgetSealUnary provenanceUnary budgetSealProvenance
  exact
    ⟨budgetWindowUnary, budgetReadbackUnary, budgetSealUnary, commonRefinementUnary,
      modulusBudgetWindow, budgetWindowReadback, budgetReadbackSeal, budgetSealProvenance,
      provenancePkg, commonRefinementPkg⟩

end BEDC.Derived.RealCauchyCompletionUp
