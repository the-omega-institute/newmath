import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityFiniteNetConsumerBoundary [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactNetRead consumerRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory consumerRead ->
          Cont handoffRead M compactNetRead ->
            Cont compactNetRead consumerRead replayRead ->
              PkgSig bundle replayRead pkg ->
                UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory compactNetRead ∧ UnaryHistory replayRead ∧
                    Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                      Cont handoffRead M compactNetRead ∧
                        Cont compactNetRead consumerRead replayRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM consumerUnary compactNetRoute replayRoute replayPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, provenancePkg, _namePkg⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed handoffUnary unaryM compactNetRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed compactNetUnary consumerUnary replayRoute
  exact
    ⟨radiusUnary, handoffUnary, compactNetUnary, replayUnary, radiusRoute, handoffRoute,
      compactNetRoute, replayRoute, provenancePkg, replayPkg⟩

end BEDC.Derived.EquicontinuityUp
