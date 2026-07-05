import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist

def LatticeStabilityCertificate (Carrier : BHist -> Prop)
    (Classifier Le : BHist -> BHist -> Prop) (meet join : BHist -> BHist -> BHist) : Prop :=
  (forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (meet a b)) ∧
    (forall {a b : BHist}, Carrier a -> Carrier b -> Carrier (join a b)) ∧
    (forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) a) ∧
    (forall {a b : BHist}, Carrier a -> Carrier b -> Le (meet a b) b) ∧
    (forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b -> Le w a -> Le w b ->
      Le w (meet a b)) ∧
    (forall {a b : BHist}, Carrier a -> Carrier b -> Le a (join a b)) ∧
    (forall {a b : BHist}, Carrier a -> Carrier b -> Le b (join a b)) ∧
    (forall {w a b : BHist}, Carrier w -> Carrier a -> Carrier b -> Le a w -> Le b w ->
      Le (join a b) w) ∧
    (forall {a a' b b' : BHist}, Classifier a a' -> Classifier b b' ->
      Classifier (meet a b) (meet a' b')) ∧
    (forall {a a' b b' : BHist}, Classifier a a' -> Classifier b b' ->
      Classifier (join a b) (join a' b'))

theorem LatticeStabilityCertificate_singleton :
    LatticeStabilityCertificate LatticeSingletonCarrier LatticeSingletonClassifier
      LatticeSingletonLE LatticeSingletonMeet LatticeSingletonJoin := by
  have laws := LatticeSingletonPrefix_laws
  exact
    ⟨(fun carrierA carrierB => (laws.right.left carrierA carrierB).left),
      (fun carrierA carrierB => (laws.right.left carrierA carrierB).right),
      (fun carrierA carrierB => (laws.right.right.left carrierA carrierB).left),
      (fun carrierA carrierB => (laws.right.right.left carrierA carrierB).right.left),
      (fun carrierW carrierA carrierB leWA leWB =>
        laws.right.right.right.left carrierA carrierB carrierW leWA leWB),
      (fun carrierA carrierB => (laws.right.right.left carrierA carrierB).right.right.left),
      (fun carrierA carrierB => (laws.right.right.left carrierA carrierB).right.right.right),
      (fun carrierW carrierA carrierB leAW leBW =>
        laws.right.right.right.right.left carrierA carrierB carrierW leAW leBW),
      (fun {a a' b b'} sameAA' sameBB' =>
        (laws.right.right.right.right.right sameAA' sameBB').left),
      (fun {a a' b b'} sameAA' sameBB' =>
        (laws.right.right.right.right.right sameAA' sameBB').right)⟩

end BEDC.Derived.LatticeUp
