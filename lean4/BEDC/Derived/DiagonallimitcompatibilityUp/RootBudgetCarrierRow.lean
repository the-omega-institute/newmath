import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_carrier_row [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetSource →
      PkgSig bundle budgetSource pkg →
        UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
          UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory realSeal ∧ UnaryHistory budgetSource ∧
              Cont diagonal triangle sealRow ∧ Cont diagonal dyadic budgetSource ∧
                Cont dyadic windows readback ∧ Cont readback realSeal route ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle budgetSource pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalDyadicBudgetSource budgetSourcePkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  exact
    ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
      readbackUnary, realSealUnary, budgetSourceUnary, diagonalTriangleSeal,
      diagonalDyadicBudgetSource, dyadicWindowsReadback, readbackRealSealRoute,
      provenancePkg, budgetSourcePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
