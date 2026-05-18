import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_socket_kind_route [AskSetup] [PackageSetup]
    {e a t v h c p n kindRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t kindRead ->
        PkgSig bundle kindRead pkg ->
          UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
            UnaryHistory h ∧ UnaryHistory kindRead ∧ Cont e a v ∧ Cont e t h ∧
              Cont v t kindRead ∧ hsame h n ∧ PkgSig bundle p pkg ∧
                PkgSig bundle kindRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier kindRoute kindPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, _cUnary, _pUnary, _nUnary, eAV,
    eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have kindUnary : UnaryHistory kindRead :=
    unary_cont_closed vUnary tUnary kindRoute
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, kindUnary, eAV, eTH, kindRoute, hN,
      pPkg, kindPkg⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
