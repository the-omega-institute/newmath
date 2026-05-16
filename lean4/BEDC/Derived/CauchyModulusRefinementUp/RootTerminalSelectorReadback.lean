import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRootTerminalSelectorReadback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectedA selectedB readbackA readbackB sealA sealB
      publicA publicB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selectedA ->
        Cont t w selectedB ->
          Cont selectedA q readbackA ->
            Cont selectedB q readbackB ->
              Cont readbackA e sealA ->
                Cont readbackB e sealB ->
                  Cont sealA h publicA ->
                    Cont sealB h publicB ->
                      PkgSig bundle publicA pkg ->
                        PkgSig bundle publicB pkg ->
                          hsame selectedA selectedB ∧ hsame readbackA readbackB ∧
                            hsame sealA sealB ∧ hsame publicA publicB ∧
                              PkgSig bundle p pkg ∧ PkgSig bundle publicA pkg ∧
                                PkgSig bundle publicB pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame
  intro carrier tWSelectedA tWSelectedB selectedAReadbackA selectedBReadbackB
    readbackASealA readbackBSealB sealAPublicA sealBPublicB publicAPkg publicBPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have sameSelected : hsame selectedA selectedB :=
    cont_respects_hsame (hsame_refl t) (hsame_refl w) tWSelectedA tWSelectedB
  have readbackARouteOverSelectedB : Cont selectedB q readbackA :=
    cont_hsame_transport sameSelected (hsame_refl q) (hsame_refl readbackA)
      selectedAReadbackA
  have sameReadback : hsame readbackA readbackB :=
    cont_respects_hsame (hsame_refl selectedB) (hsame_refl q) readbackARouteOverSelectedB
      selectedBReadbackB
  have sealAOverReadbackB : Cont readbackB e sealA :=
    cont_hsame_transport sameReadback (hsame_refl e) (hsame_refl sealA)
      readbackASealA
  have sameSeal : hsame sealA sealB :=
    cont_respects_hsame (hsame_refl readbackB) (hsame_refl e) sealAOverReadbackB
      readbackBSealB
  have publicAOverSealB : Cont sealB h publicA :=
    cont_hsame_transport sameSeal (hsame_refl h) (hsame_refl publicA)
      sealAPublicA
  have samePublic : hsame publicA publicB :=
    cont_respects_hsame (hsame_refl sealB) (hsame_refl h) publicAOverSealB sealBPublicB
  exact
    ⟨sameSelected, sameReadback, sameSeal, samePublic, pPkg, publicAPkg, publicBPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
