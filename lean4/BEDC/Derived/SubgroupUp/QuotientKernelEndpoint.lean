import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerQuotientKernel_left_endpoint_right_centralizer_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y ->
      SubgroupCentralizerCarrier mul a c ->
        SubgroupCentralizerQuotientKernel mul inv a (mul x c) y := by
  intro kernel centralC
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a v -> SubgroupCentralizerCarrier mul a (mul u v) :=
    certificateRows.right.right.left
  have invClosed :
      forall {u : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a (inv u) :=
    certificateRows.right.right.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have normalizesC : SubgroupCentralizerNormalizer mul inv a c :=
    SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralC
  have normalizesXC : SubgroupCentralizerNormalizer mul inv a (mul x c) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel.left normalizesC
  have centralInvC : SubgroupCentralizerCarrier mul a (inv c) :=
    invClosed centralC
  have productCentral :
      SubgroupCentralizerCarrier mul a (mul (inv c) (mul (inv x) y)) :=
    mulClosed centralInvC kernel.right.right
  have invProductSame :
      hsame (inv (mul x c)) (mul (inv c) (inv x)) :=
    BEDC.Derived.GroupUp.group_inverse_mul_reverse
      assocC leftId rightId mulCongr leftInv rightInv x c
  have displayedKernel :
      hsame (mul (inv c) (mul (inv x) y)) (mul (inv (mul x c)) y) := by
    exact hsame_trans (hsame_symm (assocC (inv c) (inv x) y))
      (mulCongr (hsame_symm invProductSame) (hsame_refl y))
  exact And.intro normalizesXC
    (And.intro kernel.right.left (carrierTransport productCentral displayedKernel))

protected theorem SubgroupCentralizerQuotientKernel_right_endpoint_right_centralizer_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y ->
      SubgroupCentralizerCarrier mul a c ->
        SubgroupCentralizerQuotientKernel mul inv a x (mul y c) := by
  intro kernel centralC
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a v -> SubgroupCentralizerCarrier mul a (mul u v) :=
    certificateRows.right.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have normalizesC : SubgroupCentralizerNormalizer mul inv a c :=
    SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralC
  have normalizesYC : SubgroupCentralizerNormalizer mul inv a (mul y c) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel.right.left normalizesC
  have productCentral :
      SubgroupCentralizerCarrier mul a (mul (mul (inv x) y) c) :=
    mulClosed kernel.right.right centralC
  have displayedKernel :
      hsame (mul (mul (inv x) y) c) (mul (inv x) (mul y c)) :=
    assocC (inv x) y c
  exact And.intro kernel.left
    (And.intro normalizesYC (carrierTransport productCentral displayedKernel))

protected theorem SubgroupCentralizerQuotientKernel_two_sided_centralizer_endpoint_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c d : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y ->
      SubgroupCentralizerCarrier mul a c -> SubgroupCentralizerCarrier mul a d ->
        SubgroupCentralizerQuotientKernel mul inv a (mul x c) (mul y d) := by
  intro kernel centralC centralD
  have leftClosed :
      SubgroupCentralizerQuotientKernel mul inv a (mul x c) y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_left_endpoint_right_centralizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel centralC
  exact
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_right_endpoint_right_centralizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv leftClosed centralD

theorem SubgroupCentralizerQuotientKernel_centralizer_endpoint_invariance
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c d : BHist} :
    SubgroupCentralizerCarrier mul a c -> SubgroupCentralizerCarrier mul a d ->
      (SubgroupCentralizerQuotientKernel mul inv a (mul x c) (mul y d) <->
        SubgroupCentralizerQuotientKernel mul inv a x y) := by
  intro centralC centralD
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have invClosed :
      forall {u : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a (inv u) :=
    certificateRows.right.right.right.left
  have centralInvC : SubgroupCentralizerCarrier mul a (inv c) :=
    invClosed centralC
  have centralInvD : SubgroupCentralizerCarrier mul a (inv d) :=
    invClosed centralD
  constructor
  · intro shiftedKernel
    have cancelledKernel :
        SubgroupCentralizerQuotientKernel mul inv a
          (mul (mul x c) (inv c)) (mul (mul y d) (inv d)) :=
      BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_two_sided_centralizer_endpoint_mul_closed_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv shiftedKernel centralInvC centralInvD
    have sameLeft : hsame (mul (mul x c) (inv c)) x := by
      exact hsame_trans (assocC x c (inv c))
        (hsame_trans (mulCongr (hsame_refl x) (rightInv c)) (rightId x))
    have sameRight : hsame (mul (mul y d) (inv d)) y := by
      exact hsame_trans (assocC y d (inv d))
        (hsame_trans (mulCongr (hsame_refl y) (rightInv d)) (rightId y))
    exact SubgroupCentralizerQuotientKernel_hsame_transport
      assocC leftId rightId mulCongr leftInv rightInv cancelledKernel sameLeft sameRight
  · intro kernel
    exact
      BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_two_sided_centralizer_endpoint_mul_closed_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv kernel centralC centralD

theorem SubgroupCentralizerQuotientKernel_centralizer_representative_step
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x c : BHist} :
    SubgroupCentralizerNormalizer mul inv a x -> SubgroupCentralizerCarrier mul a c ->
      SubgroupCentralizerQuotientKernel mul inv a x (mul x c) ∧
        SubgroupCentralizerQuotientKernel mul inv a (mul x c) x := by
  intro normalizesX centralC
  have diagonal : SubgroupCentralizerQuotientKernel mul inv a x x :=
    SubgroupCentralizerNormalizer_kernel_classifier_refl
      assocC leftId rightId mulCongr leftInv rightInv normalizesX
  have rightStep : SubgroupCentralizerQuotientKernel mul inv a x (mul x c) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_right_endpoint_right_centralizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv diagonal centralC
  have leftStep : SubgroupCentralizerQuotientKernel mul inv a (mul x c) x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_left_endpoint_right_centralizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv diagonal centralC
  exact And.intro rightStep leftStep

protected theorem SubgroupCentralizerQuotientKernel_centralizer_endpoint_mul_invariant_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c d : BHist} :
    SubgroupCentralizerCarrier mul a c -> SubgroupCentralizerCarrier mul a d ->
      (SubgroupCentralizerQuotientKernel mul inv a (mul x c) (mul y d) <->
        SubgroupCentralizerQuotientKernel mul inv a x y) := by
  exact SubgroupCentralizerQuotientKernel_centralizer_endpoint_invariance
    assocC leftId rightId mulCongr leftInv rightInv

end BEDC.Derived.SubgroupUp
