import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryCarrier_root_relation_row_exposure
    [AskSetup] [PackageSetup]
    {e a t v h c p n relationRead demandRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a relationRead ->
        Cont relationRead v demandRead ->
          PkgSig bundle demandRead pkg ->
            UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧
              UnaryHistory relationRead ∧ UnaryHistory demandRead ∧ Cont e a v ∧
                Cont e a relationRead ∧ Cont relationRead v demandRead ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle demandRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eARelation relationVDemand demandPkg
  obtain ⟨eUnary, aUnary, _tUnary, vUnary, _hUnary, _cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have relationUnary : UnaryHistory relationRead :=
    unary_cont_closed eUnary aUnary eARelation
  have demandUnary : UnaryHistory demandRead :=
    unary_cont_closed relationUnary vUnary relationVDemand
  exact
    ⟨eUnary, aUnary, vUnary, relationUnary, demandUnary, eAV, eARelation,
      relationVDemand, pPkg, demandPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
