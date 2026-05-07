import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DiffFormExteriorDerivativeInputRow
    (omega eta d dplus probe tensor scalar antisym source : BHist) : Prop :=
  UnaryHistory omega ∧ UnaryHistory eta ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
    Cont d (BHist.e1 BHist.Empty) dplus ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
      UnaryHistory scalar ∧ UnaryHistory antisym ∧ UnaryHistory source

def DiffFormExteriorDerivativeCandidateLedger
    (input output degree degreeSucc probe tensor scalar : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  UnaryHistory degree ∧ UnaryHistory degreeSucc ∧
    Cont degree (BHist.e1 BHist.Empty) degreeSucc ∧
      (∃ witness : BHist, InBundle witness bundle) ∧ hsame input output ∧
        hsame probe tensor ∧ hsame tensor scalar

theorem DiffFormExteriorDerivativeInputRow_degree_shift_boundary
    {omega eta d dplus probe tensor scalar antisym source : BHist} :
    DiffFormExteriorDerivativeInputRow omega eta d dplus probe tensor scalar antisym source ->
      UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus ∧
        (hsame dplus BHist.Empty -> False) := by
  intro row
  have degreeRows :
      UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus :=
    And.intro row.right.right.left
      (And.intro row.right.right.right.left row.right.right.right.right.left)
  exact And.intro degreeRows.left
    (And.intro degreeRows.right.left
      (And.intro degreeRows.right.right
        (by
          intro raisedEmpty
          cases degreeRows.right.right
          exact not_hsame_e1_empty (append_eq_empty_iff.mp raisedEmpty).right)))

theorem DiffFormExteriorDerivativeInputRow_classifier_transport
    {omega eta d dplus probe tensor scalar antisym source omega' eta' d' dplus' probe'
      tensor' scalar' antisym' source' : BHist} :
    DiffFormExteriorDerivativeInputRow omega eta d dplus probe tensor scalar antisym source ->
      hsame omega omega' -> hsame eta eta' -> hsame d d' -> hsame dplus dplus' ->
        hsame probe probe' -> hsame tensor tensor' -> hsame scalar scalar' ->
          hsame antisym antisym' -> hsame source source' ->
            DiffFormExteriorDerivativeInputRow omega' eta' d' dplus' probe' tensor' scalar'
                antisym' source' ∧
              Cont d' (BHist.e1 BHist.Empty) dplus' := by
  intro row sameOmega sameEta sameD sameDplus sameProbe sameTensor sameScalar sameAntisym
    sameSource
  have shifted : Cont d' (BHist.e1 BHist.Empty) dplus' :=
    cont_hsame_transport sameD (hsame_refl (BHist.e1 BHist.Empty)) sameDplus
      row.right.right.right.right.left
  have transported :
      DiffFormExteriorDerivativeInputRow omega' eta' d' dplus' probe' tensor' scalar'
        antisym' source' := by
    constructor
    · exact unary_transport row.left sameOmega
    · constructor
      · exact unary_transport row.right.left sameEta
      · constructor
        · exact unary_transport row.right.right.left sameD
        · constructor
          · exact unary_transport row.right.right.right.left sameDplus
          · constructor
            · exact shifted
            · constructor
              · exact unary_transport row.right.right.right.right.right.left sameProbe
              · constructor
                · exact unary_transport row.right.right.right.right.right.right.left sameTensor
                · constructor
                  · exact unary_transport row.right.right.right.right.right.right.right.left
                      sameScalar
                  · constructor
                    · exact unary_transport row.right.right.right.right.right.right.right.right.left
                        sameAntisym
                    · exact unary_transport row.right.right.right.right.right.right.right.right.right
                        sameSource
  exact And.intro transported shifted

theorem DiffFormExteriorDerivativeLedger_classifier_transport_nonempty_boundary
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source omega2 domega2
      d2 dplus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2' antisym2 source2 : BHist}
    {probes : ProbeBundle BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
    DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source d2 probe2 tensor2
      scalar2 antisym2 source2 ->
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
    hsame probe' probe2' -> hsame tensor' tensor2' -> hsame scalar' scalar2' ->
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2 tensor2'
          scalar2 scalar2' antisym2 source2 ∧
        (hsame dplus2 BHist.Empty -> False) ∧ UnaryHistory d2 ∧ UnaryHistory antisym2 := by
  intro ledger classified sameOmega sameDomega sameD sameDplus sameProbe' sameTensor'
    sameScalar'
  have transported :
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2' tensor2
        tensor2' scalar2 scalar2' antisym2 source2 :=
    DiffFormExteriorDerivativeLedger_classifier_transport ledger classified sameOmega sameDomega
      sameD sameDplus sameProbe' sameTensor' sameScalar'
  have boundaryRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty transported
  exact And.intro transported
    (And.intro boundaryRows.right.right.right
      (And.intro boundaryRows.left transported.right.right.right.right.right.right.right.right.left))

theorem DiffFormExteriorDerivative_downstream_scope {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger targetDegree : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) targetDegree ->
            (UnaryHistory degree ∧ InBundle probe probes ∧ UnaryHistory tensor ∧
              UnaryHistory scalar ∧
                hsame ledger (append degree (append probe (append tensor (append scalar antisym))))) ∧
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                ledger degree probe tensor scalar antisym ledger ∧
                UnaryHistory targetDegree ∧
                  Cont degree (BHist.e1 BHist.Empty) targetDegree := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute targetRoute
  have coverage :=
    DiffFormRootDegreeClassifier_coverage scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have raised :=
    DiffFormExteriorDerivative_degree_raise_ledger degreeUnary probeUnary tensorRoute
      antisymUnary scalarRoute ledgerRoute targetRoute
  exact And.intro
    (And.intro coverage.left.left
      (And.intro probeIn
        (And.intro coverage.left.right.right.left
          (And.intro coverage.left.right.right.right.left
            coverage.left.right.right.right.right))))
    (And.intro coverage.right (And.intro raised.right.left raised.right.right.left))

end BEDC.Derived.DiffFormUp
