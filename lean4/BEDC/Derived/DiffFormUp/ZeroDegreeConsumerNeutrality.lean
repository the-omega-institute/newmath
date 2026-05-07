import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

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

end BEDC.Derived.DiffFormUp
