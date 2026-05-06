import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonRingUpTailAlgebra_package :
    (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
      FpsSingletonCarrier (FpsSingletonAdd F G) ∧
        FpsSingletonCarrier (FpsSingletonMul F G)) ∧
    (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
      FpsSingletonClassifier G G' ->
        FpsSingletonClassifier (FpsSingletonAdd F G) (FpsSingletonAdd F' G') ∧
          FpsSingletonClassifier (FpsSingletonMul F G) (FpsSingletonMul F' G')) ∧
    (forall {F G H n : BHist},
      FpsSingletonClassifier
        (FpsSingletonPointwiseAdditionCoeff (FpsSingletonAdd F G) H n)
        (FpsSingletonPointwiseAdditionCoeff F (FpsSingletonAdd G H) n)) ∧
    (forall {xs ys zs : List BHist} {left right : BHist},
      FpsSingletonAddFoldSpineCarrier xs ->
        FpsSingletonAddFoldSpineCarrier ys ->
          FpsSingletonAddFoldSpineCarrier zs ->
            Cont (append (FpsSingletonAddFold xs) (FpsSingletonAddFold ys))
                (FpsSingletonAddFold zs) left ->
              Cont (FpsSingletonAddFold xs)
                (append (FpsSingletonAddFold ys) (FpsSingletonAddFold zs)) right ->
                FpsSingletonClassifier left right) ∧
    (forall {F G H : BHist},
      FpsSingletonClassifier (FpsSingletonMul F (FpsSingletonAdd G H))
          (FpsSingletonAdd (FpsSingletonMul F G) (FpsSingletonMul F H)) ∧
        FpsSingletonClassifier (FpsSingletonMul (FpsSingletonAdd F G) H)
          (FpsSingletonAdd (FpsSingletonMul F H) (FpsSingletonMul G H))) := by
  constructor
  · intro F G carrierF carrierG
    exact fps_singleton_empty_schema_laws.right.right.right.right.left carrierF carrierG
  · constructor
    · intro F G F' G' sameF sameG
      exact fps_singleton_empty_schema_laws.right.right.right.right.right sameF sameG
    · constructor
      · intro F G H n
        exact FpsSingletonPointwiseAdditionCoeff_assoc_classifier.left
      · constructor
        · intro xs ys zs left right xsSpine ysSpine zsSpine leftCont rightCont
          exact FpsSingletonCauchyProduct_carried_assoc_continuation_classifier
            xsSpine ysSpine zsSpine leftCont rightCont
        · intro F G H
          exact And.intro FpsSingletonCauchyProduct_distributes_over_addition_classifier.left
            FpsSingletonCauchyProduct_distributes_over_addition_classifier.right.left

end BEDC.Derived.FpsUp
