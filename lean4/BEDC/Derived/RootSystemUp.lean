import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.RootSystemUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

def RootSystemFiniteSupportCarrier
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (h : BHist) : Prop :=
  InBundle h support ∧ Vector h ∧ Nonzero h

def RootSystemFiniteSupportClassifier
    (support : ProbeBundle BHist)
    (VectorClassifier : BHist -> BHist -> Prop)
    (h k : BHist) : Prop :=
  InBundle h support ∧ InBundle k support ∧ hsame h k ∧ VectorClassifier h k

theorem RootSystemFiniteSupportCarrier_classifier_transport
    {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    {VectorClassifier : BHist -> BHist -> Prop}
    (vector_transport :
      forall {h k : BHist}, Vector h -> VectorClassifier h k -> Vector k)
    (nonzero_transport : forall {h k : BHist}, Nonzero h -> hsame h k -> Nonzero k)
    {h k : BHist} :
    RootSystemFiniteSupportCarrier support Vector Nonzero h ->
      RootSystemFiniteSupportClassifier support VectorClassifier h k ->
        RootSystemFiniteSupportCarrier support Vector Nonzero k := by
  intro carrierH classifiedHK
  exact And.intro classifiedHK.right.left
    (And.intro
      (vector_transport carrierH.right.left classifiedHK.right.right.right)
      (nonzero_transport carrierH.right.right classifiedHK.right.right.left))

end BEDC.Derived.RootSystemUp
