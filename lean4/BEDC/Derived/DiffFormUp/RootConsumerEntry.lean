import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerEntry_carrier {degree probe tensor scalar antisym ledger target : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont ledger BHist.Empty target ->
            UnaryHistory target ∧ hsame target ledger ∧ UnaryHistory tensor ∧
              UnaryHistory scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport
      (unary_append_closed coordinateRows.left
        (unary_append_closed coordinateRows.right.left
          (unary_append_closed coordinateRows.right.right.left
            (unary_append_closed coordinateRows.right.right.right.left antisymUnary))))
      (hsame_symm ledgerRoute)
  have targetLedger : hsame target ledger := targetRoute
  have targetUnary : UnaryHistory target := unary_transport ledgerUnary (hsame_symm targetLedger)
  exact ⟨targetUnary, targetLedger, coordinateRows.right.right.left,
    coordinateRows.right.right.right.left⟩

theorem DiffFormRootConsumerEntry_derivative_boundary
    {degree probe tensor scalar antisym ledger target derivativeBoundary : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont ledger BHist.Empty target ->
            Cont tensor scalar derivativeBoundary ->
              UnaryHistory tensor ∧ UnaryHistory scalar ∧ UnaryHistory derivativeBoundary ∧
                hsame derivativeBoundary (append tensor scalar) := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
    derivativeRoute
  have carrierRows :=
    DiffFormRootConsumerEntry_carrier degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute targetRoute
  have derivativeUnary : UnaryHistory derivativeBoundary :=
    unary_cont_closed carrierRows.right.right.left carrierRows.right.right.right derivativeRoute
  exact And.intro carrierRows.right.right.left
    (And.intro carrierRows.right.right.right
      (And.intro derivativeUnary derivativeRoute))

theorem DiffFormRootConsumerEntry_wedge
    {omega domega degree degreePlus probe probe' tensor tensor' scalar scalar' antisym source
      wedge : BHist} :
    DiffFormExteriorDerivativeLedger omega domega degree degreePlus probe probe' tensor tensor'
        scalar scalar' antisym source ->
      DiffFormWedgeDegreeLedger degree degreePlus wedge omega domega tensor ->
        UnaryHistory degree ∧ UnaryHistory degreePlus ∧
          Cont degree (BHist.e1 BHist.Empty) degreePlus ∧ Cont degree degreePlus wedge ∧
            UnaryHistory wedge ∧ hsame omega domega ∧ UnaryHistory tensor := by
  intro derivativeLedger wedgeLedger
  have degreeRows := DiffFormExteriorDerivativeLedger_degree_raise derivativeLedger
  exact
    ⟨degreeRows.left,
      degreeRows.right.left,
      degreeRows.right.right,
      wedgeLedger.right.right.left,
      wedgeLedger.right.right.right.left,
      wedgeLedger.right.right.right.right.right,
      wedgeLedger.right.right.right.right.left⟩

theorem DiffFormRootConsumerEntry_threshold {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop} (scalarCert : NameCert ScalarCarrier
      ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger target dplus outDegree rightLedger tensorLedger
      derivativeBoundary scalarLeft scalarRight : BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
        UnaryHistory degree ->
          UnaryHistory probe ->
            Cont degree probe tensor ->
              UnaryHistory antisym ->
                Cont tensor antisym scalar ->
                  hsame ledger
                    (append degree (append probe (append tensor (append scalar antisym)))) ->
                    Cont ledger BHist.Empty target ->
                      Cont degree (BHist.e1 BHist.Empty) dplus ->
                        Cont degree dplus outDegree ->
                          UnaryHistory rightLedger ->
                            hsame ledger rightLedger ->
                              UnaryHistory tensorLedger ->
                                Cont tensor scalar derivativeBoundary ->
                                  ScalarClassifier scalarLeft scalar ->
                                    ScalarClassifier scalar scalarRight ->
                                      UnaryHistory target ∧ hsame target ledger ∧
                                        DiffFormWedgeDegreeLedger degree dplus outDegree ledger
                                          rightLedger tensorLedger ∧
                                          DiffFormExteriorDerivativeLedger scalar dplus degree
                                            dplus probe probe tensor tensor scalar scalar antisym
                                            ledger ∧
                                            DiffFormBHistClassifier ScalarClassifier probes degree
                                              probe tensor scalarLeft antisym ledger degree probe
                                              tensor scalarRight antisym ledger ∧
                                              UnaryHistory derivativeBoundary := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
  intro ledgerRoute targetRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger
  intro tensorLedgerUnary derivativeRoute leftScalar rightScalar
  have carrierRows :=
    DiffFormRootConsumerEntry_carrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
      ledgerRoute targetRoute
  have routingRows :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  have crossedRows :=
    DiffFormRootConsumerFace_disjointness scalarCert routingRows.left leftScalar rightScalar
  have derivativeRows :=
    DiffFormRootConsumerEntry_derivative_boundary degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute targetRoute derivativeRoute
  exact
    ⟨carrierRows.left,
      carrierRows.right.left,
      routingRows.right.right,
      routingRows.right.left,
      crossedRows.left,
      derivativeRows.right.right.left⟩

end BEDC.Derived.DiffFormUp
