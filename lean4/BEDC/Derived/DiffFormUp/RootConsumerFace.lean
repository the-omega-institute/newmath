import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerFace_coverage {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus ->
            DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                ledger degree probe tensor scalar antisym ledger ∧
              UnaryHistory dplus ∧
                DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
                  scalar scalar antisym ledger := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor
  have classifierRows :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
        degree probe tensor scalar antisym ledger :=
    DiffFormBHistClassifier_reflexivity_obligation scalarCert probeIn scalarCarrier
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have dplusUnary : UnaryHistory dplus :=
    unary_cont_closed degreeUnary (unary_e1_closed unary_empty) degreeSuccessor
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport
      (unary_append_closed degreeUnary
        (unary_append_closed probeUnary
          (unary_append_closed carrierRows.right.right.left
            (unary_append_closed carrierRows.right.right.right.left antisymUnary))))
      (hsame_symm ledgerRoute)
  have exteriorLedger :
      DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor scalar
        scalar antisym ledger :=
    ⟨carrierRows.right.right.right.left, dplusUnary, carrierRows.left, dplusUnary,
      degreeSuccessor, hsame_refl probe, hsame_refl tensor, hsame_refl scalar, antisymUnary,
      ledgerUnary⟩
  exact ⟨classifierRows, dplusUnary, exteriorLedger⟩

theorem DiffFormRootConsumerPackage_carrier_projection {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus ->
            UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
              UnaryHistory scalar ∧
                DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                  DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                    tensor scalar scalar antisym ledger := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have coverageRows :=
    DiffFormRootConsumerFace_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor
  exact ⟨carrierRows.left, carrierRows.right.left, carrierRows.right.right.left,
    carrierRows.right.right.right.left, coverageRows.left, coverageRows.right.right⟩

end BEDC.Derived.DiffFormUp
