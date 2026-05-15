import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_completion_consumer_route_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectedA selectedB readbackA readbackB sealA sealB
      endpointA endpointB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selectedA ->
        Cont t w selectedB ->
          Cont selectedA q readbackA ->
            Cont selectedB q readbackB ->
              Cont readbackA e sealA ->
                Cont readbackB e sealB ->
                  Cont sealA h endpointA ->
                    Cont sealB h endpointB ->
                      PkgSig bundle endpointA pkg ->
                        PkgSig bundle endpointB pkg ->
                          hsame selectedA selectedB /\ hsame readbackA readbackB /\
                            hsame sealA sealB /\ hsame endpointA endpointB /\
                              PkgSig bundle endpointA pkg /\ PkgSig bundle endpointB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro _carrier tWSelectedA tWSelectedB selectedQReadbackA selectedQReadbackB
    readbackESealA readbackESealB sealHEndpointA sealHEndpointB endpointPkgA endpointPkgB
  have sameSelected : hsame selectedA selectedB :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) tWSelectedA tWSelectedB
  have sameReadback : hsame readbackA readbackB :=
    cont_respects_hsame sameSelected (hsame_refl q) selectedQReadbackA
      selectedQReadbackB
  have sameSeal : hsame sealA sealB :=
    cont_respects_hsame sameReadback (hsame_refl e) readbackESealA readbackESealB
  have sameEndpoint : hsame endpointA endpointB :=
    cont_respects_hsame sameSeal (hsame_refl h) sealHEndpointA sealHEndpointB
  exact ⟨sameSelected, sameReadback, sameSeal, sameEndpoint, endpointPkgA, endpointPkgB⟩

end BEDC.Derived.CauchyModulusRefinementUp
