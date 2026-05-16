import BEDC.Derived.QuotientSoundnessBoundaryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_downstream_nonescape [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer downstreamRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            Cont transportRead consumer downstreamRead ->
              PkgSig bundle refusalRead pkg ->
                PkgSig bundle transportRead pkg ->
                  PkgSig bundle downstreamRead pkg ->
                    UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                      UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory refusalRead ∧
                        UnaryHistory transportRead ∧ UnaryHistory consumer ∧
                          UnaryHistory downstreamRead ∧ Cont e a v ∧ Cont e t h ∧
                            Cont v t refusalRead ∧ Cont t h transportRead ∧
                              Cont h c consumer ∧ Cont transportRead consumer downstreamRead ∧
                                PkgSig bundle p pkg ∧ PkgSig bundle refusalRead pkg ∧
                                  PkgSig bundle transportRead pkg ∧
                                    PkgSig bundle downstreamRead pkg ∧ hsame h n ∧
                                      (Cont downstreamRead (BHist.e0 hostTail) transportRead ->
                                        False) ∧
                                        (Cont downstreamRead (BHist.e1 hostTail)
                                            transportRead ->
                                          False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vTRefusal tHTransport hCConsumer transportConsumerDownstream refusalPkg
    transportPkg downstreamPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, _nUnary, eAV, eTH,
    _hCN, pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary tHTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed transportUnary consumerUnary transportConsumerDownstream
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, refusalUnary, transportUnary,
      consumerUnary, downstreamUnary, eAV, eTH, vTRefusal, tHTransport, hCConsumer,
      transportConsumerDownstream, pPkg, refusalPkg, transportPkg, downstreamPkg, hN,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left transportConsumerDownstream hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right transportConsumerDownstream hostReturn)⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
