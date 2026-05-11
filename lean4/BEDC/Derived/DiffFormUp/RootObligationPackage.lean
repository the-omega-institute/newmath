import BEDC.Derived.DiffFormUp
import BEDC.Derived.DiffFormUp.RootConsumerFace
import BEDC.Derived.DiffFormUp.WedgeProbeConcatenation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootCarrierSource_obligation {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
                Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact
    ⟨carrierRows.left,
      carrierRows.right.left,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left,
      carrierRows.right.right.right.right,
      tensorRoute,
      scalarRoute⟩

theorem DiffFormRootWedgeProbe_obligation
    {leftDegree rightDegree outDegree leftLedger rightLedger tensorLedger : BHist}
    {left right : ProbeBundle BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
          tensorLedger ->
        SemanticNameCert
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            hsame ∧
          hsame tensorLedger (append leftLedger rightLedger) ∧
            Cont leftDegree rightDegree outDegree ∧ UnaryHistory outDegree := by
  intro probeLedger degreeLedger
  have coverage := DiffFormWedgeProbeConcatenationLedger_coverage probeLedger
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro outDegree degreeLedger
      · intro row _source
        exact hsame_refl row
      · intro row other same
        exact hsame_symm same
      · intro row other third leftSame rightSame
        exact hsame_trans leftSame rightSame
      · intro row other same source
        exact
          (DiffFormWedgeDegreeLedger_classifier_stability source (hsame_refl leftDegree)
            (hsame_refl rightDegree) same).left
    · intro _row source
      exact source
    · intro _row source
      exact source
  exact
    ⟨cert,
      coverage.right.right.right,
      degreeLedger.right.right.left,
      degreeLedger.right.right.right.left⟩

theorem DiffFormRootDownstreamConsumption_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger omega
      domega probePrime tensorPrime scalarPrime : BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
      UnaryHistory degree ->
      UnaryHistory probe ->
      UnaryHistory antisym ->
      Cont degree probe tensor ->
      Cont tensor antisym scalar ->
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
      Cont degree (BHist.e1 BHist.Empty) dplus ->
      DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ->
      DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
        tensorPrime scalar scalarPrime antisym ledger ->
        DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger
            degree probe tensor scalar antisym ledger ∧
          DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
            tensorPrime scalar scalarPrime antisym ledger ∧
            DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ∧
              (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary _probeUnary _antisymUnary _tensorRoute _scalarRoute
    _ledgerRoute _degreeStep wedgeLedger derivativeLedger
  have classifierRows :=
    DiffFormBHistClassifier_reflexivity_obligation (d := degree) (p := probe)
      (t := tensor) (s := scalar) (a := antisym) (l := ledger) scalarCert probeIn scalarCarrier
  have boundaryRows := DiffFormExteriorDerivativeLedger_degree_successor_nonempty derivativeLedger
  exact ⟨classifierRows, derivativeLedger, wedgeLedger, boundaryRows.right.right.right⟩

theorem DiffFormRootWedgeLedger_obligation {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop} (scalarCert : NameCert ScalarCarrier
      ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree ->
      UnaryHistory probe -> Cont degree probe tensor -> UnaryHistory antisym ->
        Cont tensor antisym scalar ->
          hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
            Cont degree (BHist.e1 BHist.Empty) dplus ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  ledger degree probe tensor scalar antisym ledger ∧
                DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                    tensor scalar scalar antisym ledger ∧
                  UnaryHistory tensor ∧ UnaryHistory scalar := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor
  have face :=
    DiffFormRootConsumerFace_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact
    ⟨face.left,
      face.right.right,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left⟩

theorem DiffFormRootObligationPackage_visible_source_surface {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop} (scalarCert : NameCert ScalarCarrier
      ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus : BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
        UnaryHistory degree ->
          UnaryHistory probe ->
            UnaryHistory antisym ->
              Cont degree probe tensor ->
                Cont tensor antisym scalar ->
                  hsame ledger
                      (append degree (append probe (append tensor (append scalar antisym)))) ->
                    Cont degree (BHist.e1 BHist.Empty) dplus ->
                      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                          antisym ledger degree probe tensor scalar antisym ledger ∧
                        UnaryHistory tensor ∧
                          UnaryHistory scalar ∧
                            hsame ledger
                              (append degree
                                (append probe (append tensor (append scalar antisym)))) ∧
                              Cont degree probe tensor ∧
                                Cont tensor antisym scalar ∧
                                  (hsame dplus BHist.Empty -> False) := by
  intro probeIn scalarCarrier degreeUnary probeUnary antisymUnary tensorRoute scalarRoute
    ledgerRoute degreeSuccessor
  have face :=
    DiffFormRootConsumerFace_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have dplusNonempty : hsame dplus BHist.Empty -> False := by
    intro raisedEmpty
    cases degreeSuccessor
    exact not_hsame_e1_empty (append_eq_empty_iff.mp raisedEmpty).right
  exact
    ⟨face.left,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left,
      carrierRows.right.right.right.right,
      tensorRoute,
      scalarRoute,
      dplusNonempty⟩

end BEDC.Derived.DiffFormUp
