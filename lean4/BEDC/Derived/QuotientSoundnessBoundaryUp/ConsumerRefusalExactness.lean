import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_consumer_refusal_exactness [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧
                    UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                      UnaryHistory consumer ∧ Cont e a v ∧ Cont v t refusalRead ∧
                        Cont t h transportRead ∧ Cont h c consumer ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle n pkg ∧ PkgSig bundle refusalRead pkg ∧
                            PkgSig bundle transportRead pkg ∧ PkgSig bundle consumer pkg ∧
                              hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary, eAV,
    _eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact
    ⟨eUnary, aUnary, vUnary, refusalUnary, transportUnary, consumerUnary, eAV,
      vTRefusal, tHTransport, hCConsumer, pPkg, nPkg, refusalPkg, transportPkg,
      consumerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
