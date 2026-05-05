import BEDC.Derived.NormUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp
import BEDC.Derived.MetricUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.NormUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.Derived.MetricUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def HilbertSingletonInnerProduct (_m _n : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem HilbertSingleton_inner_product_norm_compatibility {m : BHist} :
    VecSpaceSingletonCarrier m ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) ∧
        (RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
          (BHist.e1 (BHist.e1 BHist.Empty)) ↔ VecSpaceSingletonClassifier m BHist.Empty) := by
  intro carrierM
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro realClassifier (NormSingletonEmptyHistory_zero_exactness carrierM)

theorem HilbertSingleton_constant_inner_product_transport {m m' n n' : BHist} :
    VecSpaceSingletonClassifier m m' -> VecSpaceSingletonClassifier n n' ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct m' n')
            (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
            (HilbertSingletonInnerProduct m' n') ∧
            RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
              (HilbertSingletonInnerProduct m' m') := by
  intro _classifiedM _classifiedN
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (BHist.e1 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  have leftConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have rightConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m' n')
        (BHist.e1 (BHist.e1 BHist.Empty)) := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have transported :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
        (HilbertSingletonInnerProduct m' n') := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  have normTransport :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
        (HilbertSingletonInnerProduct m' m') := by
    unfold HilbertSingletonInnerProduct
    exact realClassifier
  exact And.intro leftConstant
    (And.intro rightConstant
      (And.intro transported normTransport))

theorem HilbertSingleton_endpoint_readback {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryClassifier (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          MetricDistanceWitness m n BHist.Empty := by
  intro carrierM carrierN
  have normRows := NormSingletonEmptyHistory_laws carrierM carrierN
  have innerRows := HilbertSingleton_inner_product_norm_compatibility carrierM
  have mEndpoint : hsame m BHist.Empty := normRows.right.right.right.left.right.right
  have nEndpoint : hsame n BHist.Empty := normRows.right.right.right.right.right.right
  have distanceWitness : MetricDistanceWitness m n BHist.Empty :=
    (MetricDistanceWitness_empty_distance_iff (x := m) (y := n)).mpr
      (And.intro mEndpoint nEndpoint)
  have innerConstant :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr innerRows.right normRows.right.right.right.left
  exact And.intro normRows.right.left (And.intro innerConstant distanceWitness)

end BEDC.Derived.HilbertUp
