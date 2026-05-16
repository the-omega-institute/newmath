import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_refusal_transport_determinacy
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer consumerPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont h c consumerPrime ->
              hsame consumer consumerPrime ->
                PkgSig bundle refusalRead pkg ->
                  PkgSig bundle transportRead pkg ->
                    PkgSig bundle consumer pkg ->
                      PkgSig bundle consumerPrime pkg ->
                        UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                          UnaryHistory consumer ∧ UnaryHistory consumerPrime ∧
                            hsame consumer consumerPrime ∧ Cont e t h ∧
                              Cont v t refusalRead ∧ Cont t h transportRead ∧
                                Cont h c consumer ∧ Cont h c consumerPrime ∧
                                  PkgSig bundle consumer pkg ∧
                                    PkgSig bundle consumerPrime pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer hCConsumerPrime sameConsumer
    _refusalPkg _transportPkg consumerPkg consumerPrimePkg
  obtain ⟨_eUnary, _aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _eAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have consumerPrimeUnary : UnaryHistory consumerPrime :=
    unary_cont_closed hUnary cUnary hCConsumerPrime
  exact
    ⟨refusalUnary, transportUnary, consumerUnary, consumerPrimeUnary, sameConsumer,
      eTH, vTRefusal, tHTransport, hCConsumer, hCConsumerPrime, consumerPkg,
      consumerPrimePkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
