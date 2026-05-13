import BEDC.Derived.RealCauchyCompletionUp

namespace BEDC.Derived.RealCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyCompletionCarrier_null_tail_budget_correspondence [AskSetup] [PackageSetup]
    {family modulus diagonal window readback dyadic sealRow provenance localCert nullTail
      dyadicBudget zeroTailSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyCompletionCarrier family modulus diagonal window readback dyadic sealRow
        provenance localCert bundle pkg →
      UnaryHistory nullTail →
        Cont readback nullTail dyadicBudget →
          Cont dyadicBudget sealRow zeroTailSurface →
            PkgSig bundle zeroTailSurface pkg →
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory dyadicBudget ∧
                UnaryHistory zeroTailSurface ∧ Cont readback nullTail dyadicBudget ∧
                  Cont dyadicBudget sealRow zeroTailSurface ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle zeroTailSurface pkg := by
  intro carrier nullTailUnary readbackNullTailBudget budgetSealSurface zeroTailSurfacePkg
  obtain ⟨familyUnary, modulusUnary, windowUnary, dyadicUnary, _provenanceUnary,
    familyModulusDiagonal, diagonalWindowReadback, readbackDyadicSeal,
    _sealLocalProvenance, provenancePkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed familyUnary modulusUnary familyModulusDiagonal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowUnary diagonalWindowReadback
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicSeal
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed readbackUnary nullTailUnary readbackNullTailBudget
  have zeroTailSurfaceUnary : UnaryHistory zeroTailSurface :=
    unary_cont_closed dyadicBudgetUnary sealUnary budgetSealSurface
  exact
    ⟨readbackUnary, sealUnary, dyadicBudgetUnary, zeroTailSurfaceUnary,
      readbackNullTailBudget, budgetSealSurface, provenancePkg, zeroTailSurfacePkg⟩

end BEDC.Derived.RealCauchyCompletionUp
