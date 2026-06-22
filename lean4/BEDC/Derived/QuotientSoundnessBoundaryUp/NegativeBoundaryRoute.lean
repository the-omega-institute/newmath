import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_negative_boundary_route [AskSetup] [PackageSetup]
    {e a t v h c p n representativeRead refusalRead replacementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a representativeRead ->
        Cont representativeRead v refusalRead ->
          Cont h c replacementRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle replacementRead pkg ->
                UnaryHistory representativeRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory replacementRead ∧ Cont e a representativeRead ∧
                    Cont representativeRead v refusalRead ∧ Cont h c replacementRead ∧
                      PkgSig bundle refusalRead pkg ∧
                        PkgSig bundle replacementRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier representativeRoute refusalRoute replacementRoute refusalPkg replacementPkg
  obtain ⟨eUnary, aUnary, _tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have representativeUnary : UnaryHistory representativeRead :=
    unary_cont_closed eUnary aUnary representativeRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed representativeUnary vUnary refusalRoute
  have replacementUnary : UnaryHistory replacementRead :=
    unary_cont_closed hUnary cUnary replacementRoute
  exact
    ⟨representativeUnary, refusalUnary, replacementUnary, representativeRoute,
      refusalRoute, replacementRoute, refusalPkg, replacementPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
