import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_kernel_consumer_audit_triad [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont e a v →
        Cont v t refusalRead →
          Cont t h transportRead →
            Cont h c endpoint →
              PkgSig bundle refusalRead pkg →
                PkgSig bundle endpoint pkg →
                  UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory endpoint ∧ Cont e a v ∧ Cont v t refusalRead ∧
                      Cont e t h ∧ Cont t h transportRead ∧ Cont h c endpoint ∧
                        PkgSig bundle refusalRead pkg ∧ PkgSig bundle endpoint pkg ∧
                          hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier eAV vTRefusal tHTransport hCEndpoint refusalPkg endpointPkg
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed hUnary cUnary hCEndpoint
  exact
    ⟨refusalUnary, transportUnary, endpointUnary, eAV, vTRefusal, eTH, tHTransport,
      hCEndpoint, refusalPkg, endpointPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
