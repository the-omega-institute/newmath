import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem EquicontinuityFiniteNetConsumerBoundary_compact_net_radius_replay
    [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactNetRead consumerRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory consumerRead ->
          Cont handoffRead M compactNetRead ->
            Cont compactNetRead consumerRead replayRead ->
              PkgSig bundle compactNetRead pkg ->
                PkgSig bundle replayRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨
                          hsame row P ∨ hsame row compactNetRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K F radiusRead ∧
                          Cont radiusRead rho handoffRead ∧
                            Cont handoffRead M compactNetRead ∧
                              Cont compactNetRead consumerRead replayRead ∧
                                PkgSig bundle compactNetRead pkg ∧
                                  PkgSig bundle replayRead pkg)
                      hsame ∧
                    UnaryHistory compactNetRead ∧ UnaryHistory replayRead ∧
                      Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                        Cont handoffRead M compactNetRead ∧
                          Cont compactNetRead consumerRead replayRead ∧
                            PkgSig bundle compactNetRead pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier unaryM consumerUnary compactNetRoute replayRoute compactNetPkg replayPkg
  obtain ⟨_radiusUnary, _handoffUnary, compactNetUnary, radiusRoute, handoffRoute,
    compactNetRouteExact, _pkgP, compactNetPkgExact⟩ :=
    EquicontinuityCarrier_compact_net_radius_exactness carrier unaryM compactNetRoute
      compactNetPkg
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed compactNetUnary consumerUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row M ∨ hsame row P ∨
              hsame row compactNetRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
              Cont handoffRead M compactNetRead ∧
                Cont compactNetRead consumerRead replayRead ∧
                  PkgSig bundle compactNetRead pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, radiusRoute, handoffRoute, compactNetRouteExact, replayRoute,
          compactNetPkgExact, replayPkg⟩
  }
  exact
    ⟨cert, compactNetUnary, replayUnary, radiusRoute, handoffRoute, compactNetRouteExact,
      replayRoute, compactNetPkgExact, replayPkg⟩

end BEDC.Derived.EquicontinuityUp
