import BEDC.Derived.FiniteWitnessedRefutationUp

namespace BEDC.Derived.FiniteWitnessedRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWitnessedRefutationCarrier_single_carrier_alignment [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg ->
      Cont decision route publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory key ∧ UnaryHistory decision ∧ UnaryHistory publicRead ∧
            Cont regularity gap key ∧ Cont key witness decision ∧
              Cont decision route publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier decisionRoutePublic publicPkg
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  exact
    ⟨keyUnary, decisionUnary, publicUnary, regularityGapKey, keyWitnessDecision,
      decisionRoutePublic, provenancePkg, namePkg, publicPkg⟩

end BEDC.Derived.FiniteWitnessedRefutationUp
