import BEDC.Derived.DiffFormUp.WedgeProbeConcatenation

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootRow_downstream_boundary
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger leftDegree rightDegree outDegree leftLedger
      rightLedger tensorLedger omega domega d dplus probeD probeD' tensorD tensorD' scalarD
      scalarD' antisymD sourceD : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
            tensorLedger ->
            DiffFormExteriorDerivativeLedger omega domega d dplus probeD probeD' tensorD tensorD'
              scalarD scalarD' antisymD sourceD ->
              (UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                  UnaryHistory scalar ∧
                    DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar
                      antisym ledger degree probe tensor scalar antisym ledger) ∧
                (DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger
                    rightLedger tensorLedger ∧ hsame leftLedger rightLedger) ∧
                  (UnaryHistory d ∧ UnaryHistory dplus ∧
                    Cont d (BHist.e1 BHist.Empty) dplus) := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute wedgeLedger derivativeLedger
  have rootRows :=
    DiffFormRootDegreeClassifier_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute
  have wedgeRows :=
    DiffFormWedgeDegreeLedger_classifier_stability wedgeLedger (hsame_refl leftDegree)
      (hsame_refl rightDegree) (hsame_refl outDegree)
  have derivativeRows :=
    DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  exact
    ⟨⟨rootRows.left.left, rootRows.left.right.left, rootRows.left.right.right.left,
        rootRows.left.right.right.right.left, rootRows.right⟩,
      wedgeRows, derivativeRows⟩

theorem DiffFormRootBHistNameCert_semantic_name_certificate
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          SemanticNameCert
            (fun candidate : BHist =>
              UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                UnaryHistory scalar ∧
                  hsame candidate (append degree
                    (append probe (append tensor (append scalar antisym)))))
            (fun candidate : BHist =>
              UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                UnaryHistory scalar ∧
                  hsame candidate (append degree
                    (append probe (append tensor (append scalar antisym)))))
            (fun candidate : BHist =>
              UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
                UnaryHistory scalar ∧
                  hsame candidate (append degree
                    (append probe (append tensor (append scalar antisym)))))
            hsame := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute
  have rootRows :=
    DiffFormRootDegreeClassifier_coverage scalarCert probeIn scalarCarrier degreeUnary probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute
  constructor
  · constructor
    · exact Exists.intro ledger
        ⟨rootRows.left.left, rootRows.left.right.left, rootRows.left.right.right.left,
          rootRows.left.right.right.right.left, ledgerRoute⟩
    · intro candidate _carrier
      exact hsame_refl candidate
    · intro left right same
      exact hsame_symm same
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right same carrier
      cases same
      exact carrier
  · intro _candidate source
    exact source
  · intro _candidate source
    exact source

theorem DiffFormRootRow_wedge_scope
    {left right : ProbeBundle BHist}
    {leftLedger rightLedger tensorLedger leftDegree rightDegree outDegree : BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
        tensorLedger ->
        bundleLength (bundleAppend left right) = bundleLength left + bundleLength right ∧
          (forall probe : BHist,
            InBundle probe (bundleAppend left right) <-> InBundle probe left ∨
              InBundle probe right) ∧
            Cont leftDegree rightDegree outDegree ∧ UnaryHistory outDegree ∧
              hsame tensorLedger (append leftLedger rightLedger) ∧
                hsame leftLedger rightLedger := by
  intro probeLedger degreeLedger
  have coverage := DiffFormWedgeProbeConcatenationLedger_coverage probeLedger
  exact And.intro coverage.left
    (And.intro coverage.right.left
      (And.intro degreeLedger.right.right.left
        (And.intro degreeLedger.right.right.right.left
          (And.intro coverage.right.right.right
            degreeLedger.right.right.right.right.right))))

theorem DiffFormRootRow_derivative_scope
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor'
      scalar scalar' antisym source ->
      UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
        Cont d (BHist.e1 BHist.Empty) dplus ∧ hsame probe probe' ∧
          hsame tensor tensor' ∧ hsame scalar scalar' ∧ UnaryHistory antisym ∧
            UnaryHistory source ∧ (hsame dplus BHist.Empty -> False) := by
  intro ledger
  have successorRows := DiffFormExteriorDerivativeLedger_degree_successor_nonempty ledger
  exact And.intro ledger.left
    (And.intro ledger.right.left
      (And.intro ledger.right.right.left
        (And.intro ledger.right.right.right.left
          (And.intro ledger.right.right.right.right.left
            (And.intro ledger.right.right.right.right.right.left
              (And.intro ledger.right.right.right.right.right.right.left
                (And.intro ledger.right.right.right.right.right.right.right.left
                  (And.intro ledger.right.right.right.right.right.right.right.right.left
                    (And.intro ledger.right.right.right.right.right.right.right.right.right
                      successorRows.right.right.right)))))))))

end BEDC.Derived.DiffFormUp
