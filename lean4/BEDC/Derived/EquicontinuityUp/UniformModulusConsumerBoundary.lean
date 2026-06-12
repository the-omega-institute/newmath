import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCarrier_uniform_modulus_consumer_boundary [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          Cont handoffRead M modulusRead ->
            Cont modulusRead T finiteBoundary ->
              PkgSig bundle finiteBoundary pkg ->
                UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory modulusRead ∧ UnaryHistory finiteBoundary ∧
                    Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                      Cont handoffRead M modulusRead ∧
                        Cont modulusRead T finiteBoundary ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle finiteBoundary pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM unaryT handoffModulus modulusFinite finitePkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM handoffModulus
  have finiteBoundaryUnary : UnaryHistory finiteBoundary :=
    unary_cont_closed modulusUnary unaryT modulusFinite
  exact
    ⟨radiusUnary, handoffUnary, modulusUnary, finiteBoundaryUnary, radiusRoute,
      handoffRoute, handoffModulus, modulusFinite, pkgP, finitePkg⟩

theorem EquicontinuityCarrier_uniform_modulus_finite_boundary_chain [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead uniformRead modulusRead finiteBoundary :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          Cont radiusRead rho uniformRead ->
            Cont uniformRead M handoffRead ->
              Cont handoffRead M modulusRead ->
                Cont modulusRead T finiteBoundary ->
                  PkgSig bundle finiteBoundary pkg ->
                    UnaryHistory uniformRead ∧ UnaryHistory handoffRead ∧
                      UnaryHistory modulusRead ∧ UnaryHistory finiteBoundary ∧
                        Cont K F radiusRead ∧ Cont radiusRead rho uniformRead ∧
                          Cont uniformRead M handoffRead ∧
                            Cont handoffRead M modulusRead ∧
                              Cont modulusRead T finiteBoundary ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle finiteBoundary pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM unaryT radiusUniform uniformHandoff handoffModulus modulusFinite
    finitePkg
  obtain ⟨uniformUnary, handoffUnary, radiusRoute, radiusUniformRoute, uniformHandoffRoute,
    pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_uniform_modulus_handoff carrier unaryM radiusUniform uniformHandoff
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM handoffModulus
  have finiteBoundaryUnary : UnaryHistory finiteBoundary :=
    unary_cont_closed modulusUnary unaryT modulusFinite
  exact
    ⟨uniformUnary, handoffUnary, modulusUnary, finiteBoundaryUnary, radiusRoute,
      radiusUniformRoute, uniformHandoffRoute, handoffModulus, modulusFinite, pkgP,
        finitePkg⟩

theorem EquicontinuityCarrier_transport_replay_uniform_boundary [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead consumerRead finiteBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory T ->
        Cont handoffRead R consumerRead ->
          Cont consumerRead T finiteBoundary ->
            PkgSig bundle consumerRead pkg ->
              PkgSig bundle finiteBoundary pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                        hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                          hsame row handoffRead ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont handoffRead R consumerRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle consumerRead pkg)
                    hsame ∧
                  UnaryHistory consumerRead ∧ UnaryHistory finiteBoundary ∧
                    Cont handoffRead R consumerRead ∧ Cont consumerRead T finiteBoundary ∧
                      PkgSig bundle consumerRead pkg ∧ PkgSig bundle finiteBoundary pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryT consumerRoute boundaryRoute consumerPkg boundaryPkg
  obtain ⟨consumerCert, consumerUnary⟩ :=
    EquicontinuityCarrier_transport_replay_provenance carrier consumerRoute consumerPkg
  have boundaryUnary : UnaryHistory finiteBoundary :=
    unary_cont_closed consumerUnary unaryT boundaryRoute
  exact
    ⟨consumerCert, consumerUnary, boundaryUnary, consumerRoute, boundaryRoute, consumerPkg,
      boundaryPkg⟩

end BEDC.Derived.EquicontinuityUp
