import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MarkovChainBHistTransitionCarrier [AskSetup] [PackageSetup]
    (prob time rv law kernel ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧ UnaryHistory time ∧ UnaryHistory rv ∧ UnaryHistory law ∧
    UnaryHistory kernel ∧ Cont kernel rv ledger ∧ Cont ledger law endpoint ∧
      PkgSig bundle endpoint pkg

theorem MarkovChainBHistTransitionCarrier_kernel_classifier_stability
    [AskSetup] [PackageSetup]
    {prob time rv law kernel ledger endpoint prob2 time2 rv2 law2 kernel2 ledger2
      endpoint2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainBHistTransitionCarrier prob time rv law kernel ledger endpoint bundle pkg ->
      hsame prob prob2 ->
        hsame time time2 ->
          hsame rv rv2 ->
            hsame law law2 ->
              hsame kernel kernel2 ->
                Cont kernel2 rv2 ledger2 ->
                  Cont ledger2 law2 endpoint2 ->
                    PkgSig bundle endpoint2 pkg ->
                      MarkovChainBHistTransitionCarrier
                          prob2 time2 rv2 law2 kernel2 ledger2 endpoint2 bundle pkg ∧
                        hsame endpoint endpoint2 := by
  intro carrier sameProb sameTime sameRv sameLaw sameKernel kernelRow2 ledgerRow2 pkgSig2
  have probUnary2 : UnaryHistory prob2 :=
    unary_transport carrier.left sameProb
  have timeUnary2 : UnaryHistory time2 :=
    unary_transport carrier.right.left sameTime
  have rvUnary2 : UnaryHistory rv2 :=
    unary_transport carrier.right.right.left sameRv
  have lawUnary2 : UnaryHistory law2 :=
    unary_transport carrier.right.right.right.left sameLaw
  have kernelUnary2 : UnaryHistory kernel2 :=
    unary_transport carrier.right.right.right.right.left sameKernel
  have sameLedger : hsame ledger ledger2 :=
    cont_respects_hsame sameKernel sameRv carrier.right.right.right.right.right.left
      kernelRow2
  have sameEndpoint : hsame endpoint endpoint2 :=
    cont_respects_hsame sameLedger sameLaw carrier.right.right.right.right.right.right.left
      ledgerRow2
  exact
    ⟨⟨probUnary2, timeUnary2, rvUnary2, lawUnary2, kernelUnary2, kernelRow2, ledgerRow2,
        pkgSig2⟩,
      sameEndpoint⟩

end BEDC.Derived.MarkovChainUp
