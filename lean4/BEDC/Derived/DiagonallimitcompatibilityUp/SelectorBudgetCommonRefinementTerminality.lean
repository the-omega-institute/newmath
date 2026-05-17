import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorBudgetCommonRefinementTerminality
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector criterion uniform common terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory criterion →
        UnaryHistory uniform →
          Cont diagonal windows selector →
            Cont selector criterion common →
              Cont common uniform terminal →
                PkgSig bundle terminal pkg →
                  UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory selector ∧
                    UnaryHistory criterion ∧ UnaryHistory uniform ∧ UnaryHistory common ∧
                      UnaryHistory terminal ∧ Cont diagonal windows selector ∧
                        Cont selector criterion common ∧ Cont common uniform terminal ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier criterionUnary uniformUnary diagonalWindowsSelector selectorCriterionCommon
    commonUniformTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have commonUnary : UnaryHistory common :=
    unary_cont_closed selectorUnary criterionUnary selectorCriterionCommon
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed commonUnary uniformUnary commonUniformTerminal
  exact
    ⟨diagonalUnary, windowsUnary, selectorUnary, criterionUnary, uniformUnary, commonUnary,
      terminalUnary, diagonalWindowsSelector, selectorCriterionCommon, commonUniformTerminal,
      provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
