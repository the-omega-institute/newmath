import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_representative_demand_exposure
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v h refusalRead ->
        Cont h c consumer ->
          PkgSig bundle refusalRead pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory refusalRead ∧
                UnaryHistory consumer ∧ Cont e a v ∧ Cont v h refusalRead ∧
                  Cont h c consumer ∧ PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧
                    PkgSig bundle consumer pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vHRefusal hCConsumer _refusalPkg consumerPkg
  obtain ⟨_eUnary, aUnary, _tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact
    ⟨aUnary, vUnary, refusalUnary, consumerUnary, eAV, vHRefusal, hCConsumer, pPkg,
      nPkg, consumerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
