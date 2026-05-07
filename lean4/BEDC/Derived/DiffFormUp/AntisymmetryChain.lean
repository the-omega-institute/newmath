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

theorem DiffFormAntisymmetryBoundary_derham_consumption_separation
    {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source chain degreeR
      probeR tensorR scalarR antisymR ledgerR : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
        scalar' antisym source ->
      DiffFormAntisymmetryChainLedger probes chain d probe tensor scalar antisym source degreeR
        probeR tensorR scalarR antisymR ledgerR ->
        UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
          DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source degreeR probeR
            tensorR scalarR antisymR ledgerR := by
  intro derivativeLedger chainLedger
  have degreeRows := DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  exact And.intro degreeRows.left
    (And.intro degreeRows.right.left
      (And.intro degreeRows.right.right
        chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right))

theorem DiffFormAntisymmetryChainLedger_coverage
    {probes : ProbeBundle BHist}
    {chain degree probe tensor scalar antisym ledger degreeR probeR tensorR scalarR antisymR ledgerR :
      BHist} :
    DiffFormAntisymmetryChainLedger probes chain degree probe tensor scalar antisym ledger degreeR
        probeR tensorR scalarR antisymR ledgerR ->
      UnaryHistory chain ∧ Cont degree probe tensor ∧ Cont tensor antisym scalar ∧
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
          hsame ledgerR
            (append degreeR (append probeR (append tensorR (append scalarR antisymR)))) ∧
            DiffFormBHistClassifier hsame probes degree probe tensor scalar antisym ledger degreeR
              probeR tensorR scalarR antisymR ledgerR := by
  intro chainLedger
  exact And.intro chainLedger.left
    (And.intro chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.left
      (And.intro
        chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
        (And.intro
          chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
          (And.intro
            chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
            chainLedger.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right))))

theorem DiffFormAdjacentSwapInvolutionLedger_reverse_closure {probes : ProbeBundle BHist}
    {chain degree probe tensor scalar antisym ledger degreeR probeR tensorR scalarR antisymR
      ledgerR doubleChain : BHist} :
    DiffFormAntisymmetryChainLedger probes chain degree probe tensor scalar antisym ledger degreeR
        probeR tensorR scalarR antisymR ledgerR ->
      hsame degreeR degree -> hsame probeR probe -> hsame tensorR tensor ->
        hsame scalarR scalar -> hsame antisymR antisym -> hsame ledgerR ledger ->
          Cont chain chain doubleChain ->
            DiffFormAntisymmetryChainLedger probes doubleChain degree probe tensor scalar antisym
                ledger degree probe tensor scalar antisym ledger ∧
              hsame doubleChain (append chain chain) ∧
                DiffFormBHistClassifier hsame probes degree probe tensor scalar antisym ledger degree
                  probe tensor scalar antisym ledger := by
  intro chainRows sameDegree sameProbe sameTensor sameScalar sameAntisym sameLedger doubleRoute
  cases sameDegree
  cases sameProbe
  cases sameTensor
  cases sameScalar
  cases sameAntisym
  cases sameLedger
  cases doubleRoute
  have doubleUnary : UnaryHistory (append chain chain) :=
    unary_append_closed chainRows.left chainRows.left
  have sameDouble : hsame (append chain chain) (append chain chain) :=
    hsame_refl (append chain chain)
  have classifierRows :
      DiffFormBHistClassifier hsame probes degree probe tensor scalar antisym ledger degree probe
        tensor scalar antisym ledger :=
    ⟨chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      hsame_refl degree, hsame_refl probe, hsame_refl tensor, hsame_refl scalar,
      hsame_refl antisym, hsame_refl ledger⟩
  have closedLedger :
      DiffFormAntisymmetryChainLedger probes (append chain chain) degree probe tensor scalar antisym
        ledger degree probe tensor scalar antisym ledger :=
    ⟨doubleUnary,
      chainRows.right.left,
      chainRows.right.right.left,
      chainRows.right.right.right.left,
      chainRows.right.right.right.right.left,
      chainRows.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.left,
      chainRows.right.left,
      chainRows.right.right.left,
      chainRows.right.right.right.left,
      chainRows.right.right.right.right.left,
      chainRows.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      chainRows.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      classifierRows⟩
  exact ⟨closedLedger, sameDouble, classifierRows⟩

end BEDC.Derived.DiffFormUp
