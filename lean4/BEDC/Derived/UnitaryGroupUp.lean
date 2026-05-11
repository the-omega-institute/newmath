import BEDC.Derived.HilbertUp
import BEDC.Derived.LieGroupUp
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitaryGroupUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.LieGroupUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem UnitaryGroupCarrierClassifier_obligation {hilbert automorphism endpoint : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier automorphism ->
      Cont hilbert automorphism endpoint ->
        VecSpaceSingletonCarrier hilbert ∧ LieGroupSingletonCarrier automorphism ∧
          Cont hilbert automorphism endpoint ∧ hsame endpoint hilbert := by
  intro hilbertCarrier automorphismCarrier endpointRow
  have endpointReadback : hsame endpoint hilbert := by
    cases automorphismCarrier
    exact cont_right_unit_result endpointRow
  exact And.intro hilbertCarrier
    (And.intro automorphismCarrier (And.intro endpointRow endpointReadback))

theorem UnitaryGroupCarrier_classifier_obligation
    {hilbert hilbert' automorphism automorphism' source source' target target' : BHist} :
    UnaryHistory hilbert -> UnaryHistory automorphism -> hsame hilbert hilbert' ->
      hsame automorphism automorphism' -> Cont hilbert automorphism source ->
        Cont hilbert' automorphism' source' -> Cont automorphism hilbert target ->
          Cont automorphism' hilbert' target' ->
            UnaryHistory hilbert' ∧ UnaryHistory automorphism' ∧
              hsame source source' ∧ hsame target target' := by
  intro unaryHilbert unaryAutomorphism sameHilbert sameAutomorphism sourceRow sourceRow'
    targetRow targetRow'
  have unaryHilbert' : UnaryHistory hilbert' :=
    unary_transport unaryHilbert sameHilbert
  have unaryAutomorphism' : UnaryHistory automorphism' :=
    unary_transport unaryAutomorphism sameAutomorphism
  have sameSource : hsame source source' :=
    cont_respects_hsame sameHilbert sameAutomorphism sourceRow sourceRow'
  have sameTarget : hsame target target' :=
    cont_respects_hsame sameAutomorphism sameHilbert targetRow targetRow'
  exact And.intro unaryHilbert'
    (And.intro unaryAutomorphism' (And.intro sameSource sameTarget))

theorem UnitaryGroupSourceClassifier_obligation
    {hilbert automorphism preservation source endpoint : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier automorphism ->
      UnaryHistory preservation -> Cont hilbert automorphism source ->
        Cont source preservation endpoint ->
          UnaryHistory endpoint ∧ hsame source hilbert ∧
            hsame endpoint (append source preservation) := by
  intro hilbertCarrier automorphismCarrier preservationUnary sourceRow endpointRow
  have sourceReadback : hsame source hilbert := by
    cases automorphismCarrier
    exact cont_right_unit_result sourceRow
  have hilbertUnary : UnaryHistory hilbert :=
    unary_transport unary_empty (hsame_symm hilbertCarrier)
  have sourceUnary : UnaryHistory source :=
    unary_transport hilbertUnary (hsame_symm sourceReadback)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary preservationUnary endpointRow
  exact And.intro endpointUnary (And.intro sourceReadback endpointRow)

theorem UnitaryGroupOperation_stability_obligation
    {left left' right right' product product' inverse inverse' identity identity' : BHist} :
    hsame inverse inverse' -> hsame identity identity' -> hsame right right' ->
      Cont inverse identity left -> Cont inverse' identity' left' ->
        Cont left right product -> Cont left' right' product' ->
          hsame left left' ∧ hsame product product' := by
  intro sameInverse sameIdentity sameRight inverseIdentityRow inverseIdentityRow'
    productRow productRow'
  have sameLeft : hsame left left' :=
    cont_respects_hsame sameInverse sameIdentity inverseIdentityRow inverseIdentityRow'
  have sameProduct : hsame product product' :=
    cont_respects_hsame sameLeft sameRight productRow productRow'
  exact And.intro sameLeft sameProduct

theorem UnitaryGroupOperation_preservation_obligation {hilbert left right product endpoint : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier left ->
      LieGroupSingletonCarrier right -> Cont left right product -> Cont hilbert product endpoint ->
        UnaryHistory product ∧ UnaryHistory endpoint ∧
          hsame product BHist.Empty ∧ hsame endpoint hilbert := by
  intro hilbertCarrier leftCarrier rightCarrier productRow endpointRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame leftCarrier rightCarrier productRow (cont_left_unit BHist.Empty)
  have hilbertUnary : UnaryHistory hilbert :=
    unary_transport unary_empty (hsame_symm hilbertCarrier)
  have productUnary : UnaryHistory product :=
    unary_transport unary_empty (hsame_symm productEmpty)
  have endpointHilbert : hsame endpoint hilbert :=
    by
      cases productEmpty
      exact cont_right_unit_result endpointRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport hilbertUnary (hsame_symm endpointHilbert)
  exact And.intro productUnary
    (And.intro endpointUnary (And.intro productEmpty endpointHilbert))

theorem UnitaryGroupLedger_exactness_obligation
    {hilbert hilbert' automorphism automorphism' source source' target target' : BHist} :
    VecSpaceSingletonClassifier hilbert hilbert' ->
      LieGroupSingletonClassifier automorphism automorphism' ->
        Cont hilbert automorphism source -> Cont hilbert' automorphism' source' ->
          Cont automorphism hilbert target -> Cont automorphism' hilbert' target' ->
            hsame source source' ∧ hsame target target' ∧
              RealConstantHistoryClassifier (HilbertSingletonInnerProduct hilbert automorphism)
                (HilbertSingletonInnerProduct hilbert' automorphism') ∧
                hsame source BHist.Empty ∧ hsame target BHist.Empty := by
  intro hilbertClassified automorphismClassified sourceRow sourceRow' targetRow targetRow'
  have sameSource : hsame source source' :=
    cont_respects_hsame hilbertClassified.right.right automorphismClassified.right.right
      sourceRow sourceRow'
  have sameTarget : hsame target target' :=
    cont_respects_hsame automorphismClassified.right.right hilbertClassified.right.right
      targetRow targetRow'
  have innerTransport :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct hilbert automorphism)
        (HilbertSingletonInnerProduct hilbert' automorphism') :=
    (HilbertSingleton_constant_inner_product_transport hilbertClassified
      (And.intro automorphismClassified.left
        (And.intro automorphismClassified.right.left automorphismClassified.right.right))).right.right.left
  have sourceEmpty : hsame source BHist.Empty := by
    have sourceToHilbert : hsame source hilbert :=
      cont_right_unit_result (by
        cases automorphismClassified.left
        exact sourceRow)
    exact hsame_trans sourceToHilbert hilbertClassified.left
  have targetEmpty : hsame target BHist.Empty := by
    have targetToAutomorphism : hsame target automorphism :=
      cont_right_unit_result (by
        cases hilbertClassified.left
        exact targetRow)
    exact hsame_trans targetToAutomorphism automorphismClassified.left
  exact And.intro sameSource
    (And.intro sameTarget
      (And.intro innerTransport (And.intro sourceEmpty targetEmpty)))

theorem UnitaryGroupPublicNameCert_export {hilbert automorphism source target endpoint : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier automorphism ->
      Cont hilbert automorphism source -> Cont automorphism hilbert target ->
        Cont source target endpoint ->
          SemanticNameCert (fun row : BHist => hsame row endpoint)
            (fun row : BHist => hsame row endpoint)
            (fun row : BHist => hsame row endpoint) hsame ∧
            UnaryHistory endpoint ∧ hsame source hilbert ∧ hsame target automorphism := by
  intro hilbertCarrier automorphismCarrier sourceRow targetRow endpointRow
  have sourceReadback : hsame source hilbert := by
    cases automorphismCarrier
    exact cont_right_unit_result sourceRow
  have targetReadback : hsame target automorphism := by
    cases hilbertCarrier
    exact cont_right_unit_result targetRow
  have sourceEmpty : hsame source BHist.Empty :=
    hsame_trans sourceReadback hilbertCarrier
  have targetEmpty : hsame target BHist.Empty :=
    hsame_trans targetReadback automorphismCarrier
  have endpointEmpty : hsame endpoint BHist.Empty :=
    cont_respects_hsame sourceEmpty targetEmpty endpointRow (cont_left_unit BHist.Empty)
  have endpointUnary : UnaryHistory endpoint :=
    unary_transport unary_empty (hsame_symm endpointEmpty)
  have endpointCert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _sameEndpoint
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same sameEndpoint
        exact hsame_trans (hsame_symm same) sameEndpoint
    }
    pattern_sound := by
      intro _row sameEndpoint
      exact sameEndpoint
    ledger_sound := by
      intro _row sameEndpoint
      exact sameEndpoint
  }
  exact And.intro endpointCert
    (And.intro endpointUnary (And.intro sourceReadback targetReadback))

theorem UnitaryGroupUp_StdBridge
    {hilbert automorphism source target endpoint bridgeLedger : BHist} :
    VecSpaceSingletonCarrier hilbert -> LieGroupSingletonCarrier automorphism ->
      Cont hilbert automorphism source -> Cont automorphism hilbert target ->
        Cont source target endpoint -> Cont endpoint automorphism bridgeLedger ->
          SemanticNameCert (fun row : BHist => hsame row endpoint)
            (fun row : BHist => hsame row endpoint)
            (fun row : BHist => hsame row endpoint) hsame ∧
            UnaryHistory bridgeLedger ∧ hsame source hilbert ∧
              hsame target automorphism ∧
                hsame bridgeLedger (append endpoint automorphism) := by
  intro hilbertCarrier automorphismCarrier sourceRow targetRow endpointRow bridgeLedgerRow
  have exported :=
    UnitaryGroupPublicNameCert_export hilbertCarrier automorphismCarrier sourceRow targetRow
      endpointRow
  have automorphismUnary : UnaryHistory automorphism :=
    unary_transport unary_empty (hsame_symm automorphismCarrier)
  have bridgeLedgerUnary : UnaryHistory bridgeLedger :=
    unary_cont_closed exported.right.left automorphismUnary bridgeLedgerRow
  exact
    ⟨exported.left, bridgeLedgerUnary, exported.right.right.left,
      exported.right.right.right, bridgeLedgerRow⟩

theorem UnitaryGroupInnerProduct_preservation_obligation
    {hilbert hilbert' automorphism automorphism' inner inner' transported transported' :
      BHist} :
    UnaryHistory hilbert -> UnaryHistory automorphism -> hsame hilbert hilbert' ->
      hsame automorphism automorphism' -> Cont hilbert automorphism inner ->
        Cont hilbert' automorphism' inner' -> Cont automorphism inner transported ->
          Cont automorphism' inner' transported' ->
            UnaryHistory hilbert' ∧ UnaryHistory automorphism' ∧
              hsame inner inner' ∧ hsame transported transported' := by
  intro unaryHilbert unaryAutomorphism sameHilbert sameAutomorphism innerRow innerRow'
    transportedRow transportedRow'
  have unaryHilbert' : UnaryHistory hilbert' :=
    unary_transport unaryHilbert sameHilbert
  have unaryAutomorphism' : UnaryHistory automorphism' :=
    unary_transport unaryAutomorphism sameAutomorphism
  have sameInner : hsame inner inner' :=
    cont_respects_hsame sameHilbert sameAutomorphism innerRow innerRow'
  have sameTransported : hsame transported transported' :=
    cont_respects_hsame sameAutomorphism sameInner transportedRow transportedRow'
  exact And.intro unaryHilbert'
    (And.intro unaryAutomorphism' (And.intro sameInner sameTransported))

end BEDC.Derived.UnitaryGroupUp
