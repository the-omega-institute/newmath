import BEDC.FKernel.Cont

namespace BEDC.Derived.ConvexSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ConvexSetSingletonAffineSpine : List BHist -> BHist -> Prop
  | [], z => hsame z BHist.Empty
  | x :: xs, z =>
      hsame x BHist.Empty ∧
        exists tail : BHist, ConvexSetSingletonAffineSpine xs tail ∧ Cont x tail z

theorem ConvexSetSingletonAffineSpine_closure {xs : List BHist} {z : BHist} :
    ConvexSetSingletonAffineSpine xs z -> hsame z BHist.Empty := by
  intro spine
  induction xs generalizing z with
  | nil =>
      exact spine
  | cons x xs ih =>
      cases spine with
      | intro xEmpty tailData =>
          cases tailData with
          | intro tail tailPack =>
              cases tailPack with
              | intro tailSpine continuation =>
                  have tailEmpty : hsame tail BHist.Empty := ih tailSpine
                  exact hsame_trans continuation (append_eq_empty_iff.mpr
                    (And.intro xEmpty tailEmpty))

theorem ConvexSetSingletonAffineSpine_midpoint_closure {x y endpoint : BHist} :
    hsame x BHist.Empty -> hsame y BHist.Empty -> Cont x y endpoint ->
      ConvexSetSingletonAffineSpine [x, y] endpoint ∧ hsame endpoint BHist.Empty := by
  intro xEmpty yEmpty endpointRow
  have tailSpine : ConvexSetSingletonAffineSpine [y] y :=
    And.intro yEmpty (Exists.intro BHist.Empty
      (And.intro (hsame_refl BHist.Empty) (cont_right_unit y)))
  have spine : ConvexSetSingletonAffineSpine [x, y] endpoint :=
    And.intro xEmpty (Exists.intro y (And.intro tailSpine endpointRow))
  exact And.intro spine (ConvexSetSingletonAffineSpine_closure spine)

theorem ConvexSetPointwiseIntersection_affine_combination_closure
    {C D NonNeg : BHist -> Prop}
    {add scalarAdd scalarAction : BHist -> BHist -> BHist}
    {one a b x y : BHist}
    (closedC :
      forall {a b x y : BHist}, C x -> C y -> NonNeg a -> NonNeg b ->
        hsame (scalarAdd a b) one -> C (add (scalarAction a x) (scalarAction b y)))
    (closedD :
      forall {a b x y : BHist}, D x -> D y -> NonNeg a -> NonNeg b ->
        hsame (scalarAdd a b) one -> D (add (scalarAction a x) (scalarAction b y))) :
    C x ∧ D x -> C y ∧ D y -> NonNeg a -> NonNeg b -> hsame (scalarAdd a b) one ->
      C (add (scalarAction a x) (scalarAction b y)) ∧
        D (add (scalarAction a x) (scalarAction b y)) := by
  intro xData yData nonnegA nonnegB unitSum
  exact And.intro
    (closedC xData.left yData.left nonnegA nonnegB unitSum)
    (closedD xData.right yData.right nonnegA nonnegB unitSum)

theorem ConvexSetLinearImage_affine_combination_closure
    {C Image NonNeg : BHist -> Prop}
    {ClassifierW : BHist -> BHist -> Prop}
    {addV addW scalarAdd scalarActionV scalarActionW f : BHist -> BHist -> BHist}
    {one a b u v : BHist}
    (image_elim :
      forall {target : BHist}, Image target ->
        exists source : BHist, C source ∧ ClassifierW (f source source) target)
    (image_intro :
      forall {source target : BHist}, C source -> ClassifierW (f source source) target ->
        Image target)
    (closedC :
      forall {a b x y : BHist}, C x -> C y -> NonNeg a -> NonNeg b ->
        hsame (scalarAdd a b) one -> C (addV (scalarActionV a x) (scalarActionV b y)))
    (mapAffine :
      forall {a b x y u v : BHist}, C x -> C y -> ClassifierW (f x x) u ->
        ClassifierW (f y y) v -> NonNeg a -> NonNeg b -> hsame (scalarAdd a b) one ->
          ClassifierW
            (f (addV (scalarActionV a x) (scalarActionV b y))
              (addV (scalarActionV a x) (scalarActionV b y)))
            (addW (scalarActionW a u) (scalarActionW b v))) :
    Image u -> Image v -> NonNeg a -> NonNeg b -> hsame (scalarAdd a b) one ->
      Image (addW (scalarActionW a u) (scalarActionW b v)) := by
  intro imageU imageV nonnegA nonnegB unitSum
  cases image_elim imageU with
  | intro sourceU sourceUData =>
      cases image_elim imageV with
      | intro sourceV sourceVData =>
          have sourceClosed :
              C (addV (scalarActionV a sourceU) (scalarActionV b sourceV)) :=
            closedC sourceUData.left sourceVData.left nonnegA nonnegB unitSum
          have mapped :
              ClassifierW
                (f (addV (scalarActionV a sourceU) (scalarActionV b sourceV))
                  (addV (scalarActionV a sourceU) (scalarActionV b sourceV)))
                (addW (scalarActionW a u) (scalarActionW b v)) :=
            mapAffine sourceUData.left sourceVData.left sourceUData.right sourceVData.right
              nonnegA nonnegB unitSum
          exact image_intro sourceClosed mapped

end BEDC.Derived.ConvexSetUp
