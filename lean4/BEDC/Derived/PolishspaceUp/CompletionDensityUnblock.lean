import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompletionDensityUnblock [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName densityRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont metric separable densityRoute →
        PkgSig bundle densityRoute pkg →
          UnaryHistory metric ∧ UnaryHistory complete ∧ UnaryHistory separable ∧
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory densityRoute ∧
              Cont metric separable densityRoute ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle densityRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier metricSeparableDensity densityPkg
  rcases carrier with
    ⟨metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary, _ledgerUnary,
      _alignmentUnary, _transportUnary, _metricCompleteAlignment, _alignmentStreamReadback,
      _ledgerTransportRoute, provenancePkg⟩
  have densityUnary : UnaryHistory densityRoute :=
    unary_cont_closed metricUnary separableUnary metricSeparableDensity
  exact
    ⟨metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary, densityUnary,
      metricSeparableDensity, provenancePkg, densityPkg⟩

end BEDC.Derived.PolishspaceUp
