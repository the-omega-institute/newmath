import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_filter_basis_route [AskSetup] [PackageSetup]
    {M R D W H C P N basisRead cauchyBasisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg ->
      Cont R D basisRead ->
        Cont basisRead C cauchyBasisRead ->
          PkgSig bundle cauchyBasisRead pkg ->
            UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
              UnaryHistory C ∧ UnaryHistory basisRead ∧ UnaryHistory cauchyBasisRead ∧
                Cont R D basisRead ∧ Cont basisRead C cauchyBasisRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle cauchyBasisRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier basisRoute cauchyBasisRoute cauchyBasisPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have basisReadUnary : UnaryHistory basisRead :=
    unary_cont_closed radiusUnary dyadicUnary basisRoute
  have cauchyBasisReadUnary : UnaryHistory cauchyBasisRead :=
    unary_cont_closed basisReadUnary replayUnary cauchyBasisRoute
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, replayUnary, basisReadUnary,
      cauchyBasisReadUnary, basisRoute, cauchyBasisRoute, provenancePkg, cauchyBasisPkg⟩

end BEDC.Derived.FormalBallUp
