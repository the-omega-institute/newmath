import BEDC.Derived.DiffFormUp.RootConsumerSourceProjection
import BEDC.Derived.DiffFormUp.DownstreamExteriorInput

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormWedgeDegreeLedger_consumer_boundary
    {degree degreePrime partner partnerPrime out outPrime leftLedger rightLedger tensorLedger :
      BHist} :
    DiffFormWedgeDegreeLedger degree partner out leftLedger rightLedger tensorLedger ->
      hsame degree degreePrime -> hsame partner partnerPrime -> hsame out outPrime ->
        UnaryHistory degree ∧ UnaryHistory partner ∧ UnaryHistory out ∧
          Cont degree partner out ∧
            DiffFormWedgeDegreeLedger degreePrime partnerPrime outPrime leftLedger rightLedger
              tensorLedger ∧
              hsame leftLedger rightLedger := by
  intro ledger sameDegree samePartner sameOut
  have transported :=
    DiffFormWedgeDegreeLedger_classifier_stability ledger sameDegree samePartner sameOut
  exact
    ⟨ledger.left, ledger.right.left, ledger.right.right.right.left, ledger.right.right.left,
      transported.left, transported.right⟩

theorem DiffFormExteriorConsumer_boundary {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger omega
      domega probePrime tensorPrime scalarPrime : BHist}
    {probes : ProbeBundle BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
      UnaryHistory degree ->
      UnaryHistory probe ->
      UnaryHistory antisym ->
      Cont degree probe tensor ->
      Cont tensor antisym scalar ->
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
      DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ->
      DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
        tensorPrime scalar scalarPrime antisym ledger ->
        UnaryHistory degree ∧ UnaryHistory dplus ∧ UnaryHistory outDegree ∧
          Cont degree dplus outDegree ∧ hsame ledger rightLedger ∧
            DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
              tensorPrime scalar scalarPrime antisym ledger ∧
              (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary probeUnary antisymUnary tensorRoute scalarRoute
    ledgerRoute wedgeLedger derivativeLedger
  have consumerRows :=
    DiffFormRootConsumer_source_projection_scope scalarCert probeIn scalarCarrier degreeUnary
      probeUnary antisymUnary tensorRoute scalarRoute ledgerRoute wedgeLedger derivativeLedger
  have wedgeBoundary :=
    DiffFormWedgeDegreeLedger_consumer_boundary wedgeLedger (hsame_refl degree)
      (hsame_refl dplus) (hsame_refl outDegree)
  have degreeBoundary :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty derivativeLedger
  exact
    ⟨consumerRows.left.left.left,
      consumerRows.right.left,
      wedgeBoundary.right.right.left,
      wedgeBoundary.right.right.right.left,
      wedgeBoundary.right.right.right.right.right,
      consumerRows.right.right.right.right.right.right.right.right.right,
      degreeBoundary.right.right.right⟩

theorem DiffFormDownstreamConsumer_boundary {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger omega
      domega probePrime tensorPrime scalarPrime : BHist}
    {probes : ProbeBundle BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
      UnaryHistory degree ->
      UnaryHistory probe ->
      UnaryHistory antisym ->
      Cont degree probe tensor ->
      Cont tensor antisym scalar ->
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
      DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ->
      DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
        tensorPrime scalar scalarPrime antisym ledger ->
        UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory degree ∧ UnaryHistory dplus ∧
          Cont degree dplus outDegree ∧ Cont degree (BHist.e1 BHist.Empty) dplus ∧
            hsame ledger rightLedger ∧ (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary probeUnary antisymUnary tensorRoute scalarRoute
    ledgerRoute wedgeLedger derivativeLedger
  have consumerBoundary :=
    DiffFormExteriorConsumer_boundary scalarCert probeIn scalarCarrier degreeUnary probeUnary
      antisymUnary tensorRoute scalarRoute ledgerRoute wedgeLedger derivativeLedger
  have exteriorInput :=
    DiffFormExteriorDerivativeLedger_downstream_input_obligation derivativeLedger
  exact
    ⟨exteriorInput.left,
      exteriorInput.right.left,
      consumerBoundary.left,
      consumerBoundary.right.left,
      consumerBoundary.right.right.right.left,
      exteriorInput.right.right.right.right.left,
      consumerBoundary.right.right.right.right.left,
      exteriorInput.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.DiffFormUp
