import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootRow_carrier_scope
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier) {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger : BHist} :
    InBundle probe probes -> ScalarCarrier scalar -> UnaryHistory degree -> UnaryHistory probe ->
      Cont degree probe tensor -> UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          (UnaryHistory tensor ∧ UnaryHistory scalar ∧ Cont degree probe tensor ∧
              Cont tensor antisym scalar) ∧
            DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym
              ledger degree probe tensor scalar antisym ledger := by
  intro probeIn scalarRow degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have classifierRows :=
    DiffFormBHistClassifier_reflexivity_obligation (d := degree) (p := probe)
      (t := tensor) (s := scalar) (a := antisym) (l := ledger) scalarCert probeIn scalarRow
  exact And.intro
    (And.intro coordinateRows.right.right.left
      (And.intro coordinateRows.right.right.right.left
        (And.intro tensorRoute scalarRoute)))
    classifierRows

end BEDC.Derived.DiffFormUp
