import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootDegreeProbeFace_coverage {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus : BHist} :
    DegreeProbeAligned degree probes -> InBundle probe probes -> ScalarCarrier scalar ->
      UnaryHistory probe -> Cont degree probe tensor -> UnaryHistory antisym ->
        Cont tensor antisym scalar ->
          hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
            Cont degree (BHist.e1 BHist.Empty) dplus ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
                    scalar scalar antisym ledger ∧
                  UnaryHistory dplus ∧ UnaryHistory degree ∧ InBundle probe probes ∧
                    UnaryHistory tensor ∧ UnaryHistory scalar := by
  intro aligned probeIn scalarCarrier probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
    degreeSuccessor
  have degreeRows :=
    DiffFormDegreeProbeAligned_hsame_transport aligned (hsame_refl degree)
  have face :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
          degree probe tensor scalar antisym ledger ∧
        UnaryHistory dplus ∧
          DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor tensor
            scalar scalar antisym ledger :=
    DiffFormRootConsumerFace_coverage scalarCert probeIn scalarCarrier degreeRows.right probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeRows.right probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro face.left
    (And.intro face.right.right
      (And.intro face.right.left
        (And.intro carrierRows.left
          (And.intro probeIn
            (And.intro carrierRows.right.right.left carrierRows.right.right.right.left)))))

end BEDC.Derived.DiffFormUp
