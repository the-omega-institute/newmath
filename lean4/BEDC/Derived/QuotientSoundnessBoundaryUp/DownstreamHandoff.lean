import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_downstream_handoff_readiness [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory n ∧
                      UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                        UnaryHistory consumer ∧ Cont e a v ∧ Cont e t h ∧
                          Cont v t refusalRead ∧ Cont t h transportRead ∧
                            Cont h c consumer ∧ PkgSig bundle p pkg ∧
                              PkgSig bundle n pkg ∧ PkgSig bundle refusalRead pkg ∧
                                PkgSig bundle transportRead pkg ∧
                                  PkgSig bundle consumer pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, nUnary, eAV,
    eTH, _hCN, pPkg, nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, nUnary, refusalUnary,
      transportUnary, consumerUnary, eAV, eTH, vTRefusal, tHTransport, hCConsumer,
      pPkg, nPkg, refusalPkg, transportPkg, consumerPkg, hN⟩

theorem QuotientSoundnessBoundary_public_bridge_nonescape [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                    UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                      UnaryHistory refusalRead ∧ UnaryHistory transportRead ∧
                        UnaryHistory consumer ∧ Cont e a v ∧ Cont e t h ∧
                          Cont v t refusalRead ∧ Cont t h transportRead ∧
                            Cont h c consumer ∧ PkgSig bundle p pkg ∧
                              PkgSig bundle n pkg ∧ PkgSig bundle refusalRead pkg ∧
                                PkgSig bundle transportRead pkg ∧
                                  PkgSig bundle consumer pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer refusalPkg transportPkg consumerPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, nUnary, eAV, eTH,
    _hCN, pPkg, nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, nUnary, refusalUnary,
      transportUnary, consumerUnary, eAV, eTH, vTRefusal, tHTransport, hCConsumer,
      pPkg, nPkg, refusalPkg, transportPkg, consumerPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
