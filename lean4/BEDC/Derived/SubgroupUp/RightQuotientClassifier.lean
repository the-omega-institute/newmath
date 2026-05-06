import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerRightQuotientClassifier_trans_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y z : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y ->
      SubgroupCentralizerRightQuotientClassifier mul inv a y z ->
        SubgroupCentralizerRightQuotientClassifier mul inv a x z := by
  intro xy yz
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelYZ :
      SubgroupCentralizerRightQuotientClassifier mul inv a y z <->
        SubgroupCentralizerQuotientKernel mul inv a y z :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelXZ :
      SubgroupCentralizerRightQuotientClassifier mul inv a x z <->
        SubgroupCentralizerQuotientKernel mul inv a x z :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  exact Iff.mpr classifierKernelXZ
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_trans_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY xy) (Iff.mp classifierKernelYZ yz))

theorem SubgroupCentralizerRightQuotientClassifier_hsame_transport
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x x' y y' : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y -> hsame x x' ->
      hsame y y' -> SubgroupCentralizerRightQuotientClassifier mul inv a x' y' := by
  intro classified sameXX' sameYY'
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelX'Y' :
      SubgroupCentralizerRightQuotientClassifier mul inv a x' y' <->
        SubgroupCentralizerQuotientKernel mul inv a x' y' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have transported : SubgroupCentralizerQuotientKernel mul inv a x' y' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_hsame_transport
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY classified) sameXX' sameYY'
  exact Iff.mpr classifierKernelX'Y' transported

theorem SubgroupCentralizerRightQuotientClassifier_diagonal_carrier_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x) {a x : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x x <->
      SubgroupCentralizerNormalizer mul inv a x := by
  constructor
  · intro diagonal
    exact diagonal.left
  · intro normalizes
    exact
      BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizerQuotientClassifier_refl_from_empty_unit
        leftId rightId normalizes

theorem SubgroupCentralizerQuotientKernel_diagonal_carrier_exactness
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x x <->
      SubgroupCentralizerNormalizer mul inv a x := by
  constructor
  · intro diagonal
    exact diagonal.left
  · intro normalizes
    exact
      SubgroupCentralizerNormalizer_kernel_classifier_refl
        assocC leftId rightId mulCongr leftInv rightInv normalizes

protected theorem SubgroupCentralizerRightQuotientClassifier_symm_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y ->
      SubgroupCentralizerRightQuotientClassifier mul inv a y x := by
  intro classified
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelYX :
      SubgroupCentralizerRightQuotientClassifier mul inv a y x <->
        SubgroupCentralizerQuotientKernel mul inv a y x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  exact Iff.mpr classifierKernelYX
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_symm_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY classified))

protected theorem SubgroupCentralizerRightQuotientClassifier_product_witness_carrier_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a u p q : BHist} :
    SubgroupCentralizerNormalizer mul inv a u -> SubgroupCentralizerCarrier mul a p ->
      SubgroupCentralizerCarrier mul a q ->
        SubgroupCentralizerCarrier mul a (mul (mul (mul (inv u) p) u) q) := by
  intro normalizesU centralP centralQ
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {s t : BHist}, SubgroupCentralizerCarrier mul a s ->
        SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerCarrier mul a (mul s t) :=
    certificateRows.right.right.left
  have carrierTransport :
      forall {s t : BHist}, SubgroupCentralizerCarrier mul a s -> hsame s t ->
        SubgroupCentralizerCarrier mul a t :=
    certificateRows.right.right.right.right
  have invInvSameU : hsame (inv (inv u)) u :=
    BEDC.Derived.GroupUp.group_left_inverse_involutive
      assocC leftId rightId mulCongr leftInv u
  have conjugatedCentral :
      SubgroupCentralizerCarrier mul a (mul (mul (inv u) p) u) :=
    carrierTransport (normalizesU.right p centralP)
      (mulCongr (hsame_refl (mul (inv u) p)) invInvSameU)
  exact mulClosed conjugatedCentral centralQ

protected theorem SubgroupCentralizerRightQuotientClassifier_product_witness_endpoint_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {x y u v p q : BHist} :
    hsame y (mul x p) -> hsame v (mul u q) ->
      hsame (mul y v) (mul (mul x u) (mul (mul (mul (inv u) p) u) q)) := by
  intro sameYP sameVQ
  have sameUA :
      hsame (mul u (mul (mul (inv u) p) u)) (mul p u) := by
    exact hsame_trans (hsame_symm (assocC u (mul (inv u) p) u))
      (hsame_trans
        (mulCongr (hsame_symm (assocC u (inv u) p)) (hsame_refl u))
        (hsame_trans
          (mulCongr (mulCongr (rightInv u) (hsame_refl p)) (hsame_refl u))
          (mulCongr (leftId p) (hsame_refl u))))
  have sameUR :
      hsame (mul u (mul (mul (mul (inv u) p) u) q)) (mul (mul p u) q) := by
    exact hsame_trans (hsame_symm (assocC u (mul (mul (inv u) p) u) q))
      (mulCongr sameUA (hsame_refl q))
  have sameExpanded :
      hsame (mul (mul x p) (mul u q)) (mul x (mul (mul p u) q)) := by
    exact hsame_trans (assocC x p (mul u q))
      (mulCongr (hsame_refl x) (hsame_symm (assocC p u q)))
  exact hsame_trans (mulCongr sameYP sameVQ)
    (hsame_trans sameExpanded
      (hsame_trans
        (mulCongr (hsame_refl x) (hsame_symm sameUR))
        (hsame_symm (assocC x u (mul (mul (mul (inv u) p) u) q)))))

theorem SubgroupCentralizerRightQuotientClassifier_mul_compatible_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y u v : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y ->
      SubgroupCentralizerRightQuotientClassifier mul inv a u v ->
        SubgroupCentralizerRightQuotientClassifier mul inv a (mul x u) (mul y v) := by
  intro leftClassified rightClassified
  cases leftClassified.right.right with
  | intro p witnessP =>
      cases rightClassified.right.right with
      | intro q witnessQ =>
          let r : BHist := mul (mul (mul (inv u) p) u) q
          have certificateRows :=
            BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
              assocC leftId rightId mulCongr leftInv rightInv (a := a)
          have mulClosed :
              forall {s t : BHist}, SubgroupCentralizerCarrier mul a s ->
                SubgroupCentralizerCarrier mul a t ->
                  SubgroupCentralizerCarrier mul a (mul s t) :=
            certificateRows.right.right.left
          have carrierTransport :
              forall {s t : BHist}, SubgroupCentralizerCarrier mul a s -> hsame s t ->
                SubgroupCentralizerCarrier mul a t :=
            certificateRows.right.right.right.right
          have normalizesXU : SubgroupCentralizerNormalizer mul inv a (mul x u) :=
            BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
              assocC leftId rightId mulCongr leftInv rightInv
              leftClassified.left rightClassified.left
          have normalizesYV : SubgroupCentralizerNormalizer mul inv a (mul y v) :=
            BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
              assocC leftId rightId mulCongr leftInv rightInv
              leftClassified.right.left rightClassified.right.left
          have invInvSameU : hsame (inv (inv u)) u :=
            BEDC.Derived.GroupUp.group_left_inverse_involutive
              assocC leftId rightId mulCongr leftInv u
          have conjugatedCentral :
              SubgroupCentralizerCarrier mul a (mul (mul (inv u) p) u) :=
            carrierTransport (rightClassified.left.right p witnessP.left)
              (mulCongr (hsame_refl (mul (inv u) p)) invInvSameU)
          have rCentral : SubgroupCentralizerCarrier mul a r :=
            mulClosed conjugatedCentral witnessQ.left
          have sameUA :
              hsame (mul u (mul (mul (inv u) p) u)) (mul p u) := by
            exact hsame_trans (hsame_symm (assocC u (mul (inv u) p) u))
              (hsame_trans
                (mulCongr (hsame_symm (assocC u (inv u) p)) (hsame_refl u))
                (hsame_trans
                  (mulCongr (mulCongr (rightInv u) (hsame_refl p)) (hsame_refl u))
                  (mulCongr (leftId p) (hsame_refl u))))
          have sameUR : hsame (mul u r) (mul (mul p u) q) := by
            exact hsame_trans (hsame_symm (assocC u (mul (mul (inv u) p) u) q))
              (mulCongr sameUA (hsame_refl q))
          have sameExpanded :
              hsame (mul (mul x p) (mul u q)) (mul x (mul (mul p u) q)) := by
            exact hsame_trans (assocC x p (mul u q))
              (mulCongr (hsame_refl x) (hsame_symm (assocC p u q)))
          have sameProduct : hsame (mul y v) (mul (mul x u) r) := by
            exact hsame_trans (mulCongr witnessP.right witnessQ.right)
              (hsame_trans sameExpanded
                (hsame_trans
                  (mulCongr (hsame_refl x) (hsame_symm sameUR))
                  (hsame_symm (assocC x u r))))
          exact And.intro normalizesXU
            (And.intro normalizesYV
              (Exists.intro r (And.intro rCentral sameProduct)))

protected theorem SubgroupCentralizerQuotientKernel_mul_compatible_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y u v : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y ->
      SubgroupCentralizerQuotientKernel mul inv a u v ->
        SubgroupCentralizerQuotientKernel mul inv a (mul x u) (mul y v) := by
  intro leftKernel rightKernel
  have kernelClassifierXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have kernelClassifierUV :
      SubgroupCentralizerRightQuotientClassifier mul inv a u v <->
        SubgroupCentralizerQuotientKernel mul inv a u v :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have kernelClassifierProduct :
      SubgroupCentralizerRightQuotientClassifier mul inv a (mul x u) (mul y v) <->
        SubgroupCentralizerQuotientKernel mul inv a (mul x u) (mul y v) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  exact Iff.mp kernelClassifierProduct
    (SubgroupCentralizerRightQuotientClassifier_mul_compatible_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mpr kernelClassifierXY leftKernel) (Iff.mpr kernelClassifierUV rightKernel))

end BEDC.Derived.SubgroupUp
