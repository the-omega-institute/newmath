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

theorem DiffFormRootSource_obligation {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          SemanticNameCert (fun row : BHist => hsame row ledger)
              (fun row : BHist => hsame row ledger)
              (fun row : BHist => hsame row ledger) hsame ∧
            UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
              UnaryHistory scalar ∧ Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger (hsame_refl ledger)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _left _right same
          exact hsame_symm same
        equiv_trans := by
          intro _left _middle _right sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _left _right same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact
    ⟨cert,
      carrierRows.left,
      carrierRows.right.left,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left,
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

theorem DiffFormRootWedgeOperation_obligation {left right : ProbeBundle BHist}
    {leftDegree rightDegree outDegree leftLedger rightLedger tensorLedger assocLeft assocRight :
      BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
          tensorLedger ->
        DiffFormWedgeDegreeLedger leftDegree outDegree assocLeft leftLedger tensorLedger
            tensorLedger ->
          DiffFormWedgeDegreeLedger outDegree rightDegree assocRight tensorLedger rightLedger
              tensorLedger ->
            bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
              (forall probe : BHist,
                InBundle probe (bundleAppend left right) <-> InBundle probe left ∨
                  InBundle probe right) ∧
                Cont leftDegree rightDegree outDegree ∧ UnaryHistory outDegree ∧
                  hsame tensorLedger (append leftLedger rightLedger) := by
  intro probeLedger degreeLedger _assocLeftLedger _assocRightLedger
  have coverage := DiffFormWedgeProbeConcatenationLedger_coverage probeLedger
  exact
    ⟨coverage.left,
      coverage.right.left,
      degreeLedger.right.right.left,
      degreeLedger.right.right.right.left,
      coverage.right.right.right⟩

theorem DiffFormRootCarrierClassifier_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger : BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
        UnaryHistory degree ->
          UnaryHistory probe ->
            Cont degree probe tensor ->
              UnaryHistory antisym ->
                Cont tensor antisym scalar ->
                  hsame ledger
                      (append degree (append probe (append tensor (append scalar antisym)))) ->
                    UnaryHistory tensor ∧ UnaryHistory scalar ∧
                      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                        antisym ledger degree probe tensor scalar antisym ledger ∧
                        Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute
  have carrierRows :=
    DiffFormBHistLedger_exactness_obligation degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have classifierRows :=
    DiffFormBHistClassifier_reflexivity_obligation (d := degree) (p := probe)
      (t := tensor) (s := scalar) (a := antisym) (l := ledger) scalarCert probeIn
      scalarCarrier
  exact
    ⟨carrierRows.left,
      carrierRows.right.left,
      classifierRows,
      carrierRows.right.right.right.left,
      carrierRows.right.right.right.right⟩

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
