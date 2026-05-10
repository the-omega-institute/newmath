import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormManifoldTensorSource_scope
    {degree probe tensor scalar antisym ledger : BHist} :
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
  have exactRows :=
    DiffFormBHistLedger_exactness_obligation degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro exactRows.left
        (And.intro exactRows.right.left
          (And.intro exactRows.right.right.left
            (And.intro exactRows.right.right.right.left exactRows.right.right.right.right)))))

theorem DiffFormWedgeContinuation_input_closure
    {leftDegree rightDegree outDegree leftProbe rightProbe tensorLeft tensorRight scalarLeft
      scalarRight antisymLeft antisymRight leftLedger rightLedger tensorLedger : BHist}
    {leftBundle rightBundle : ProbeBundle BHist} :
    DegreeProbeAligned leftDegree leftBundle -> DegreeProbeAligned rightDegree rightBundle ->
      InBundle leftProbe leftBundle -> InBundle rightProbe rightBundle ->
        UnaryHistory leftProbe -> UnaryHistory rightProbe ->
          Cont leftDegree leftProbe tensorLeft -> Cont rightDegree rightProbe tensorRight ->
            UnaryHistory antisymLeft -> UnaryHistory antisymRight ->
              Cont tensorLeft antisymLeft scalarLeft ->
                Cont tensorRight antisymRight scalarRight -> hsame leftLedger rightLedger ->
                  UnaryHistory tensorLedger -> Cont leftDegree rightDegree outDegree ->
                    DegreeProbeAligned outDegree (bundleAppend leftBundle rightBundle) ∧
                      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger
                        rightLedger tensorLedger ∧
                        UnaryHistory tensorLeft ∧ UnaryHistory tensorRight := by
  intro leftAligned rightAligned _leftIn _rightIn leftProbeUnary rightProbeUnary leftTensorRoute
    rightTensorRoute _leftAntisymUnary _rightAntisymUnary _leftScalarRoute _rightScalarRoute
    ledgerSame tensorLedgerUnary wedgeRoute
  have outAligned :=
    DiffFormDegreeProbeAligned_bundleAppend_cont leftAligned rightAligned wedgeRoute
  have leftDegreeUnary : UnaryHistory leftDegree := by
    exact (DiffFormDegreeProbeAligned_hsame_transport leftAligned (hsame_refl leftDegree)).right
  have rightDegreeUnary : UnaryHistory rightDegree := by
    exact (DiffFormDegreeProbeAligned_hsame_transport rightAligned (hsame_refl rightDegree)).right
  have outDegreeUnary : UnaryHistory outDegree :=
    unary_cont_closed leftDegreeUnary rightDegreeUnary wedgeRoute
  have tensorLeftUnary : UnaryHistory tensorLeft :=
    unary_cont_closed leftDegreeUnary leftProbeUnary leftTensorRoute
  have tensorRightUnary : UnaryHistory tensorRight :=
    unary_cont_closed rightDegreeUnary rightProbeUnary rightTensorRoute
  have wedgeLedger :
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
        tensorLedger :=
    And.intro leftDegreeUnary
      (And.intro rightDegreeUnary
        (And.intro wedgeRoute
          (And.intro outDegreeUnary (And.intro tensorLedgerUnary ledgerSame))))
  exact And.intro outAligned
    (And.intro wedgeLedger (And.intro tensorLeftUnary tensorRightUnary))

end BEDC.Derived.DiffFormUp
