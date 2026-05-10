import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormUp_StdBridge {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym' ledger'
      _wedge outDegree leftLedger rightLedger tensorLedger d dplus omega domega source : BHist} :
    InBundle probe probes -> InBundle probe' probes -> ScalarCarrier scalar ->
      ScalarClassifier scalar scalar' -> UnaryHistory degree -> UnaryHistory probe ->
        Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
          hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
            hsame degree degree' -> hsame probe probe' -> hsame tensor tensor' ->
              hsame scalar scalar' -> hsame antisym antisym' -> hsame ledger ledger' ->
                DiffFormWedgeDegreeLedger degree degree' outDegree leftLedger rightLedger
                    tensorLedger ->
                  DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor
                    tensor' scalar scalar' antisym source ->
                    SemanticNameCert (fun row : BHist => hsame row ledger')
                        (fun row : BHist => hsame row ledger')
                        (fun row : BHist => hsame row ledger') hsame ∧
                      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                          antisym ledger degree' probe' tensor' scalar' antisym' ledger' ∧
                        DiffFormWedgeDegreeLedger degree degree' outDegree leftLedger rightLedger
                            tensorLedger ∧
                          UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus := by
  intro probeIn probeIn' scalarCarrier scalarClass degreeUnary probeUnary tensorRow
    antisymUnary scalarRow ledgerRow sameDegree sameProbe sameTensor sameScalar sameAntisym
    sameLedger wedgeLedger derivativeLedger
  have transportedRows :=
    DiffFormRootDegreeClassifier_transport probeIn probeIn' scalarCarrier scalarClass degreeUnary
      probeUnary tensorRow antisymUnary scalarRow ledgerRow sameDegree sameProbe sameTensor
      sameScalar sameAntisym sameLedger
  have classifierRows :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
        degree' probe' tensor' scalar' antisym' ledger' :=
    transportedRows.right
  have scalarSelf : ScalarClassifier scalar scalar :=
    NameCert.equiv_refl scalarCert scalarCarrier
  have scalarRoundTrip : ScalarClassifier scalar scalar' :=
    NameCert.equiv_trans scalarCert scalarSelf scalarClass
  have derivativeRows :=
    DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  have ledgerCert :
      SemanticNameCert (fun row : BHist => hsame row ledger')
        (fun row : BHist => hsame row ledger')
        (fun row : BHist => hsame row ledger') hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger' (hsame_refl ledger')
      equiv_refl := by
        intro row _sameLedger
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same sameLedger'
        exact hsame_trans (hsame_symm same) sameLedger'
    }
    pattern_sound := by
      intro _row sameLedger'
      exact sameLedger'
    ledger_sound := by
      intro _row sameLedger'
      exact sameLedger'
  }
  exact ⟨ledgerCert,
    ⟨classifierRows.left, classifierRows.right.left, classifierRows.right.right.left,
      classifierRows.right.right.right.left, classifierRows.right.right.right.right.left,
      scalarRoundTrip, classifierRows.right.right.right.right.right.right.left,
      classifierRows.right.right.right.right.right.right.right⟩,
    wedgeLedger, derivativeRows.right.left,
    derivativeRows.right.right⟩

end BEDC.Derived.DiffFormUp
