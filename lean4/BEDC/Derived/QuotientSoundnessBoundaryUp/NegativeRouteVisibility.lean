import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_negative_route_visibility [AskSetup] [PackageSetup]
    {e a t v h c p n representativeRead refusalRead replacementRead visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a representativeRead ->
        Cont representativeRead v refusalRead ->
          Cont h c replacementRead ->
            Cont refusalRead t visibleRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle replacementRead pkg ->
                  PkgSig bundle visibleRead pkg ->
                    UnaryHistory representativeRead ∧ UnaryHistory refusalRead ∧
                      UnaryHistory replacementRead ∧ UnaryHistory visibleRead ∧
                        Cont e a representativeRead ∧
                          Cont representativeRead v refusalRead ∧
                            Cont h c replacementRead ∧
                              Cont refusalRead t visibleRead ∧
                                PkgSig bundle refusalRead pkg ∧
                                  PkgSig bundle replacementRead pkg ∧
                                    PkgSig bundle visibleRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier representativeRoute refusalRoute replacementRoute visibleRoute
    refusalPkg replacementPkg visiblePkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have representativeUnary : UnaryHistory representativeRead :=
    unary_cont_closed eUnary aUnary representativeRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed representativeUnary vUnary refusalRoute
  have replacementUnary : UnaryHistory replacementRead :=
    unary_cont_closed hUnary cUnary replacementRoute
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed refusalUnary tUnary visibleRoute
  exact
    ⟨representativeUnary, refusalUnary, replacementUnary, visibleUnary,
      representativeRoute, refusalRoute, replacementRoute, visibleRoute, refusalPkg,
      replacementPkg, visiblePkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
