import BEDC.Derived.HilbertUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitaryGroupUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.LieGroupUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.UnitaryGroupUp
