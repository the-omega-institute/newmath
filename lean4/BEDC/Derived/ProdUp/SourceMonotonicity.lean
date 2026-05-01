import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist

theorem ProdHistorySource_monotonicity {Left Right Left' Right' : BHist -> Prop}
    (leftWeakening : forall h : BHist, Left h -> Left' h)
    (rightWeakening : forall h : BHist, Right h -> Right' h) :
    (forall {h : BHist}, ProdHistoryCarrier Left Right h ->
      ProdHistoryCarrier Left' Right' h) /\
      (forall {h k : BHist}, ProdHistoryClassifier Left Right h k ->
        ProdHistoryClassifier Left' Right' h k) := by
  have carrierWeakening :
      forall {h : BHist}, ProdHistoryCarrier Left Right h ->
        ProdHistoryCarrier Left' Right' h := by
    intro h carrier
    cases carrier with
    | intro l restL =>
        cases restL with
        | intro r data =>
            cases data with
            | intro leftCarrier rest =>
                cases rest with
                | intro rightCarrier cont =>
                    exact Exists.intro l
                      (Exists.intro r
                        (And.intro (leftWeakening l leftCarrier)
                          (And.intro (rightWeakening r rightCarrier) cont)))
  constructor
  · exact carrierWeakening
  · intro h k classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            have carrierH' : ProdHistoryCarrier Left' Right' h :=
              carrierWeakening carrierH
            have carrierK' : ProdHistoryCarrier Left' Right' k :=
              carrierWeakening carrierK
            exact And.intro carrierH' (And.intro carrierK' sameHK)

theorem ProdHistorySource_equivalence {Left Right Left' Right' : BHist -> Prop}
    (leftEquiv : forall h : BHist, Left h <-> Left' h)
    (rightEquiv : forall h : BHist, Right h <-> Right' h) :
    (forall {h : BHist}, ProdHistoryCarrier Left Right h <->
      ProdHistoryCarrier Left' Right' h) /\
      (forall {h k : BHist}, ProdHistoryClassifier Left Right h k <->
        ProdHistoryClassifier Left' Right' h k) := by
  have forward :
      (forall {h : BHist}, ProdHistoryCarrier Left Right h ->
        ProdHistoryCarrier Left' Right' h) /\
        (forall {h k : BHist}, ProdHistoryClassifier Left Right h k ->
          ProdHistoryClassifier Left' Right' h k) :=
    ProdHistorySource_monotonicity
      (fun h leftCarrier => (leftEquiv h).mp leftCarrier)
      (fun h rightCarrier => (rightEquiv h).mp rightCarrier)
  have backward :
      (forall {h : BHist}, ProdHistoryCarrier Left' Right' h ->
        ProdHistoryCarrier Left Right h) /\
        (forall {h k : BHist}, ProdHistoryClassifier Left' Right' h k ->
          ProdHistoryClassifier Left Right h k) :=
    ProdHistorySource_monotonicity
      (fun h leftCarrier => (leftEquiv h).mpr leftCarrier)
      (fun h rightCarrier => (rightEquiv h).mpr rightCarrier)
  constructor
  · intro h
    constructor
    · exact forward.left
    · exact backward.left
  · intro h k
    constructor
    · exact forward.right
    · exact backward.right

end BEDC.Derived.ProdUp
