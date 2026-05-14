import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_shared_selector_determinacy [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectedA selectedB readbackA readbackB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selectedA →
        Cont t w selectedB →
          Cont selectedA q readbackA →
            Cont selectedB q readbackB →
              PkgSig bundle readbackA pkg →
                PkgSig bundle readbackB pkg →
                  hsame selectedA selectedB ∧ hsame readbackA readbackB ∧
                    Cont t w selectedA ∧ Cont t w selectedB ∧
                      Cont selectedA q readbackA ∧ Cont selectedB q readbackB ∧
                        PkgSig bundle readbackA pkg ∧ PkgSig bundle readbackB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro _carrier tWSelectedA tWSelectedB selectedAQReadbackA selectedBQReadbackB readbackPkgA
    readbackPkgB
  have sameSelected : hsame selectedA selectedB :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) tWSelectedA tWSelectedB
  have sameReadback : hsame readbackA readbackB :=
    cont_respects_hsame sameSelected (hsame_refl q) selectedAQReadbackA selectedBQReadbackB
  exact
    ⟨sameSelected, sameReadback, tWSelectedA, tWSelectedB, selectedAQReadbackA,
      selectedBQReadbackB, readbackPkgA, readbackPkgB⟩

end BEDC.Derived.CauchyModulusRefinementUp
