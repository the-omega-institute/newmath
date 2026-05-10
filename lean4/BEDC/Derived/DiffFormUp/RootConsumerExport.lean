import BEDC.Derived.DiffFormUp.RootConsumerFace

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerExport_no_extra_laws
    {degree probe tensor scalar antisym ledger tail : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          hsame ledger (BHist.e0 tail) -> False := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute zeroRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have targetUnary :
      UnaryHistory (append degree (append probe (append tensor (append scalar antisym)))) :=
    unary_append_closed coordinateRows.left
      (unary_append_closed coordinateRows.right.left
        (unary_append_closed coordinateRows.right.right.left
          (unary_append_closed coordinateRows.right.right.right.left antisymUnary)))
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport targetUnary (hsame_symm ledgerRoute)
  exact unary_no_zero_extension (unary_transport ledgerUnary zeroRoute)

theorem DiffFormRootConsumerExport_coverage
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source
      rootLedger exportLedger : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor'
        scalar scalar' antisym source ->
      UnaryHistory rootLedger ->
        Cont source rootLedger exportLedger ->
          UnaryHistory exportLedger ∧ hsame exportLedger (append source rootLedger) ∧
            UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory source := by
  intro ledger rootUnary exportRow
  have sourceUnary : UnaryHistory source :=
    ledger.right.right.right.right.right.right.right.right.right
  have exportUnary : UnaryHistory exportLedger :=
    unary_cont_closed sourceUnary rootUnary exportRow
  exact And.intro exportUnary
    (And.intro exportRow
      (And.intro ledger.left
        (And.intro ledger.right.left sourceUnary)))

theorem DiffFormRootConsumerExport_exactness
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {omega domega degree dplus probe probePrime tensor tensorPrime scalar scalarPrime antisym source
      rootLedger exportLedger : BHist}
    {probes : ProbeBundle BHist} :
    InBundle probe probes ->
      ScalarCarrier scalar ->
        DiffFormExteriorDerivativeLedger omega domega degree dplus probe probePrime tensor
            tensorPrime scalar scalarPrime antisym source ->
          UnaryHistory rootLedger ->
            Cont source rootLedger exportLedger ->
              DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
                  source degree probe tensor scalar antisym source ∧
                UnaryHistory exportLedger ∧ hsame exportLedger (append source rootLedger) ∧
                  UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory source := by
  intro probeIn scalarCarrier ledger rootUnary exportRow
  have classifierRows :
      DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym source
        degree probe tensor scalar antisym source :=
    DiffFormBHistClassifier_reflexivity_obligation
      (d := degree) (p := probe) (t := tensor) (s := scalar) (a := antisym)
      (l := source) scalarCert probeIn scalarCarrier
  have coverageRows :
      UnaryHistory exportLedger ∧ hsame exportLedger (append source rootLedger) ∧
        UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory source :=
    DiffFormRootConsumerExport_coverage ledger rootUnary exportRow
  exact And.intro classifierRows coverageRows

theorem DiffFormRootExport_wedge_threshold {ScalarCarrier : BHist -> Prop}
    {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger dplus outDegree rightLedger tensorLedger rootLedger
      exportLedger : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) dplus -> Cont degree dplus outDegree ->
            UnaryHistory rightLedger -> hsame ledger rightLedger -> UnaryHistory tensorLedger ->
              UnaryHistory rootLedger -> Cont ledger rootLedger exportLedger ->
                DiffFormWedgeDegreeLedger degree dplus outDegree ledger rightLedger tensorLedger ∧
                  DiffFormExteriorDerivativeLedger scalar dplus degree dplus probe probe tensor
                    tensor scalar scalar antisym ledger ∧
                    UnaryHistory exportLedger ∧ hsame exportLedger (append ledger rootLedger) := by
  intro probeIn scalarCarrier degreeUnary probeUnary tensorRoute antisymUnary scalarRoute
    ledgerRoute degreeSuccessor wedgeRoute rightLedgerUnary sameRightLedger tensorLedgerUnary
    rootLedgerUnary exportRow
  have routed :=
    DiffFormRootConsumerPackage_operation_routing scalarCert probeIn scalarCarrier degreeUnary
      probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute degreeSuccessor wedgeRoute
      rightLedgerUnary sameRightLedger tensorLedgerUnary
  obtain ⟨_, _, _, _, _, _, _, _, _, ledgerUnary⟩ := routed.right.left
  have exportUnary : UnaryHistory exportLedger :=
    unary_cont_closed ledgerUnary rootLedgerUnary exportRow
  exact ⟨routed.right.right, routed.right.left, exportUnary, exportRow⟩

end BEDC.Derived.DiffFormUp
