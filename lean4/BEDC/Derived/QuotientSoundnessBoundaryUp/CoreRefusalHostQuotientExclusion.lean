import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_core_refusal_host_quotient_exclusion
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          Cont h c endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧ UnaryHistory h ∧
                UnaryHistory c ∧ UnaryHistory refusalRead ∧ UnaryHistory endpoint ∧
                  Cont e a v ∧ Cont v h refusalRead ∧ Cont h c endpoint ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eAV vHRefusal hCEndpoint endpointPkg
  obtain ⟨eUnary, aUnary, _tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary hCEndpoint
  exact
    ⟨eUnary, aUnary, vUnary, hUnary, cUnary, refusalUnary, endpointUnary, eAV,
      vHRefusal, hCEndpoint, pPkg, endpointPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
