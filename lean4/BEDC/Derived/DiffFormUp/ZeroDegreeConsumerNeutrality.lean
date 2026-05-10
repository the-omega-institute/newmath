import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DiffFormZeroDegreeConsumerNeutralitySurface
    (degree probe tensor scalar ledger : BHist) : Prop :=
  hsame degree BHist.Empty ∧ hsame probe BHist.Empty ∧ Cont degree probe BHist.Empty ∧
    UnaryHistory tensor ∧ UnaryHistory scalar ∧ UnaryHistory ledger

theorem DiffFormZeroDegreeConsumerNeutralitySurface_hsame_transport
    {degree probe tensor scalar ledger degree' probe' tensor' scalar' ledger' : BHist} :
    DiffFormZeroDegreeConsumerNeutralitySurface degree probe tensor scalar ledger ->
      hsame degree degree' -> hsame probe probe' -> hsame tensor tensor' ->
        hsame scalar scalar' -> hsame ledger ledger' ->
          DiffFormZeroDegreeConsumerNeutralitySurface degree' probe' tensor' scalar' ledger' ∧
            Cont degree' probe' BHist.Empty := by
  intro surface sameDegree sameProbe sameTensor sameScalar sameLedger
  have degreeEmpty : hsame degree' BHist.Empty :=
    hsame_trans (hsame_symm sameDegree) surface.left
  have probeEmpty : hsame probe' BHist.Empty :=
    hsame_trans (hsame_symm sameProbe) surface.right.left
  have transportedCont : Cont degree' probe' BHist.Empty :=
    cont_hsame_transport sameDegree sameProbe (hsame_refl BHist.Empty)
      surface.right.right.left
  have tensorUnary : UnaryHistory tensor' :=
    unary_transport surface.right.right.right.left sameTensor
  have scalarUnary : UnaryHistory scalar' :=
    unary_transport surface.right.right.right.right.left sameScalar
  have ledgerUnary : UnaryHistory ledger' :=
    unary_transport surface.right.right.right.right.right sameLedger
  exact And.intro
    (And.intro degreeEmpty
      (And.intro probeEmpty
        (And.intro transportedCont
          (And.intro tensorUnary (And.intro scalarUnary ledgerUnary)))))
    transportedCont

theorem DiffFormZeroDegree_consumer_law_separation {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {probe tensor scalar antisym ledger dplus scalarLeft scalarRight : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory probe ->
      Cont BHist.Empty probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append BHist.Empty (append probe (append tensor (append scalar antisym)))) ->
          Cont BHist.Empty (BHist.e1 BHist.Empty) dplus ->
            ScalarClassifier scalarLeft scalar -> ScalarClassifier scalar scalarRight ->
              DiffFormExteriorDerivativeLedger scalar dplus BHist.Empty dplus probe probe tensor
                  tensor scalar scalar antisym ledger ∧
                DiffFormBHistClassifier ScalarClassifier probes BHist.Empty probe tensor scalarLeft
                    antisym ledger BHist.Empty probe tensor scalarRight antisym ledger ∧
                  hsame ledger ledger := by
  intro probeIn scalarCarrier probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
    degreeSuccessor leftScalar rightScalar
  have shared :
      DiffFormBHistClassifier ScalarClassifier probes BHist.Empty probe tensor scalar antisym
          ledger BHist.Empty probe tensor scalar antisym ledger ∧
        DiffFormExteriorDerivativeLedger scalar dplus BHist.Empty dplus probe probe tensor tensor
          scalar scalar antisym ledger ∧
          Cont BHist.Empty (BHist.e1 BHist.Empty) dplus :=
    DiffFormZeroDegree_shared_consumer_face scalarCert probeIn scalarCarrier probeUnary tensorRoute
      antisymUnary scalarRoute ledgerRoute degreeSuccessor
  have separated :
      DiffFormBHistClassifier ScalarClassifier probes BHist.Empty probe tensor scalarLeft antisym
          ledger BHist.Empty probe tensor scalarRight antisym ledger ∧
        hsame ledger ledger :=
    DiffFormRootConsumerFace_disjointness scalarCert shared.left leftScalar rightScalar
  exact And.intro shared.right.left separated

theorem DiffFormZeroDegree_deps_ready_consumer_seal {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {probe tensor scalar antisym ledger dplus scalarLeft scalarRight : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory probe ->
      Cont BHist.Empty probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append BHist.Empty (append probe (append tensor (append scalar antisym)))) ->
          Cont BHist.Empty (BHist.e1 BHist.Empty) dplus ->
            ScalarClassifier scalarLeft scalar -> ScalarClassifier scalar scalarRight ->
              DiffFormZeroDegreeConsumerNeutralitySurface BHist.Empty BHist.Empty tensor scalar
                  ledger ∧
                DiffFormBHistClassifier ScalarClassifier probes BHist.Empty probe tensor scalarLeft
                    antisym ledger BHist.Empty probe tensor scalarRight antisym ledger ∧
                  DiffFormExteriorDerivativeLedger scalar dplus BHist.Empty dplus probe probe
                    tensor tensor scalar scalar antisym ledger ∧
                    hsame ledger ledger := by
  intro probeIn scalarCarrier probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
    degreeSuccessor leftScalar rightScalar
  have tensorUnary : UnaryHistory tensor := by
    cases tensorRoute
    exact unary_append_closed unary_empty probeUnary
  have scalarUnary : UnaryHistory scalar := by
    cases scalarRoute
    exact unary_append_closed tensorUnary antisymUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport
      (unary_append_closed unary_empty
        (unary_append_closed probeUnary
          (unary_append_closed tensorUnary
            (unary_append_closed scalarUnary antisymUnary))))
      (hsame_symm ledgerRoute)
  have surface :
      DiffFormZeroDegreeConsumerNeutralitySurface BHist.Empty BHist.Empty tensor scalar ledger :=
    And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty)
        (And.intro (cont_intro (append_empty_right BHist.Empty).symm)
          (And.intro tensorUnary (And.intro scalarUnary ledgerUnary))))
  have separated :=
    DiffFormZeroDegree_consumer_law_separation scalarCert probeIn scalarCarrier probeUnary
      tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor leftScalar rightScalar
  exact And.intro surface
    (And.intro separated.right.left (And.intro separated.left separated.right.right))

end BEDC.Derived.DiffFormUp
