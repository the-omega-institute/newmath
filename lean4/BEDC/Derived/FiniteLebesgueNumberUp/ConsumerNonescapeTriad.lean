import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberConsumerNonescapeTriad [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead compactNetRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead nameRow compactNetRead ->
          Cont compactNetRead route uniformRead ->
            PkgSig bundle uniformRead pkg ->
              UnaryHistory compactRead ∧ UnaryHistory compactNetRead ∧
                UnaryHistory uniformRead ∧ Cont radius mesh compactRead ∧
                  Cont compactRead nameRow compactNetRead ∧
                    Cont compactNetRead route uniformRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactNameCompactNet compactNetRouteUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameCompactNet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactNetUnary routeUnary compactNetRouteUniform
  exact
    ⟨compactUnary, compactNetUnary, uniformUnary, radiusMeshCompact,
      compactNameCompactNet, compactNetRouteUniform, provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
