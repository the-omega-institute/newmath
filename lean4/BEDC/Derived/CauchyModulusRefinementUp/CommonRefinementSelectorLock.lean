import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_common_refinement_selector_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectedA selectedB readbackA readbackB sealA sealB :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selectedA ->
        Cont t w selectedB ->
          Cont selectedA q readbackA ->
            Cont selectedB q readbackB ->
              Cont readbackA e sealA ->
                Cont readbackB e sealB ->
                  PkgSig bundle sealA pkg ->
                    PkgSig bundle sealB pkg ->
                      hsame selectedA selectedB ∧ hsame readbackA readbackB ∧
                        hsame sealA sealB ∧ PkgSig bundle sealA pkg ∧
                          PkgSig bundle sealB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro _carrier tWSelectedA tWSelectedB selectedAQReadbackA selectedBQReadbackB
    readbackAESealA readbackBESealB sealPkgA sealPkgB
  have sameSelected : hsame selectedA selectedB :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) tWSelectedA tWSelectedB
  have sameReadback : hsame readbackA readbackB :=
    cont_respects_hsame sameSelected (hsame_refl q) selectedAQReadbackA selectedBQReadbackB
  have sameSeal : hsame sealA sealB :=
    cont_respects_hsame sameReadback (hsame_refl e) readbackAESealA readbackBESealB
  exact ⟨sameSelected, sameReadback, sameSeal, sealPkgA, sealPkgB⟩

end BEDC.Derived.CauchyModulusRefinementUp
