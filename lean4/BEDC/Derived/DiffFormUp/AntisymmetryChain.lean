import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def DiffFormAntisymmetryChainLedger
    (probes : ProbeBundle BHist)
    (chain degree probe tensor scalar antisym ledger degreeR probeR tensorR scalarR antisymR ledgerR :
      BHist) : Prop :=
  UnaryHistory chain ∧
    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧ UnaryHistory scalar ∧
      UnaryHistory antisym ∧ UnaryHistory ledger ∧
        UnaryHistory degreeR ∧ UnaryHistory probeR ∧ UnaryHistory tensorR ∧
          UnaryHistory scalarR ∧ UnaryHistory antisymR ∧ UnaryHistory ledgerR ∧
            Cont degree probe tensor ∧ Cont tensor antisym scalar ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
                hsame ledgerR
                  (append degreeR (append probeR (append tensorR (append scalarR antisymR)))) ∧
                  DiffFormBHistClassifier hsame probes degree probe tensor scalar antisym ledger
                    degreeR probeR tensorR scalarR antisymR ledgerR

theorem DiffFormAntisymmetryChainLedger_classifier_stability
    {probes : ProbeBundle BHist}
    {chain chain2 degree probe tensor scalar antisym ledger degreeR probeR tensorR scalarR antisymR
      ledgerR degree2 probe2 tensor2 scalar2 antisym2 ledger2 degreeR2 probeR2 tensorR2 scalarR2
      antisymR2 ledgerR2 : BHist} :
    DiffFormAntisymmetryChainLedger probes chain degree probe tensor scalar antisym ledger degreeR
        probeR tensorR scalarR antisymR ledgerR ->
      hsame degree degree2 -> hsame probe probe2 -> hsame tensor tensor2 ->
        hsame scalar scalar2 -> hsame antisym antisym2 -> hsame ledger ledger2 ->
          hsame degreeR degreeR2 -> hsame probeR probeR2 -> hsame tensorR tensorR2 ->
            hsame scalarR scalarR2 -> hsame antisymR antisymR2 -> hsame ledgerR ledgerR2 ->
              hsame chain chain2 ->
                DiffFormAntisymmetryChainLedger probes chain2 degree2 probe2 tensor2 scalar2
                    antisym2 ledger2 degreeR2 probeR2 tensorR2 scalarR2 antisymR2 ledgerR2 ∧
                  DiffFormBHistClassifier hsame probes degree2 probe2 tensor2 scalar2 antisym2
                    ledger2 degreeR2 probeR2 tensorR2 scalarR2 antisymR2 ledgerR2 := by
  intro chainRows sameDegree sameProbe sameTensor sameScalar sameAntisym sameLedger sameDegreeR
    sameProbeR sameTensorR sameScalarR sameAntisymR sameLedgerR sameChain
  cases sameDegree
  cases sameProbe
  cases sameTensor
  cases sameScalar
  cases sameAntisym
  cases sameLedger
  cases sameDegreeR
  cases sameProbeR
  cases sameTensorR
  cases sameScalarR
  cases sameAntisymR
  cases sameLedgerR
  cases sameChain
  exact ⟨chainRows, chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
