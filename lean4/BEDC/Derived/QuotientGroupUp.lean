import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp
open BEDC.FKernel.NameCert

theorem QuotientGroupCentralizerNormalizer_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SubgroupCentralizerNormalizer mul inv a BHist.Empty := by
  have invEmpty : hsame (inv BHist.Empty) BHist.Empty := by
    exact hsame_trans (hsame_symm (leftId (inv BHist.Empty))) (rightInv BHist.Empty)
  have invInvEmpty : hsame (inv (inv BHist.Empty)) BHist.Empty := by
    exact hsame_trans (hsame_symm (leftId (inv (inv BHist.Empty))))
      (hsame_trans (mulCongr (hsame_symm invEmpty) (hsame_refl (inv (inv BHist.Empty))))
        (rightInv (inv BHist.Empty)))
  constructor
  · intro x centralX
    have conjugateSame : hsame (mul (mul BHist.Empty x) (inv BHist.Empty)) x :=
      hsame_trans (mulCongr (leftId x) invEmpty) (rightId x)
    exact hsame_trans (mulCongr conjugateSame (hsame_refl a))
      (hsame_trans centralX (mulCongr (hsame_refl a) (hsame_symm conjugateSame)))
  · intro x centralX
    have conjugateSame : hsame (mul (mul (inv BHist.Empty) x)
        (inv (inv BHist.Empty))) x :=
      hsame_trans (mulCongr (mulCongr invEmpty (hsame_refl x)) invInvEmpty)
        (hsame_trans (mulCongr (leftId x) (hsame_refl BHist.Empty)) (rightId x))
    exact hsame_trans (mulCongr conjugateSame (hsame_refl a))
      (hsame_trans centralX (mulCongr (hsame_refl a) (hsame_symm conjugateSame)))

theorem QuotientGroupCentralizerNormalizer_empty_hsame_transport_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (invCongr : forall {x y : BHist}, hsame x y -> hsame (inv x) (inv y))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    hsame BHist.Empty t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro emptyT
  have emptyNormalizer := QuotientGroupCentralizerNormalizer_empty_unit
    leftId rightId mulCongr rightInv (a := a)
  constructor
  · intro x centralX
    have conjugateToEmpty : hsame (mul (mul t x) (inv t))
        (mul (mul BHist.Empty x) (inv BHist.Empty)) :=
      mulCongr (mulCongr (hsame_symm emptyT) (hsame_refl x)) (invCongr (hsame_symm emptyT))
    exact hsame_trans (mulCongr conjugateToEmpty (hsame_refl a))
      (hsame_trans (emptyNormalizer.left x centralX)
        (mulCongr (hsame_refl a) (hsame_symm conjugateToEmpty)))
  · intro x centralX
    have sameInvT : hsame (inv t) (inv BHist.Empty) := invCongr (hsame_symm emptyT)
    have conjugateToEmpty : hsame (mul (mul (inv t) x) (inv (inv t)))
        (mul (mul (inv BHist.Empty) x) (inv (inv BHist.Empty))) :=
      mulCongr (mulCongr sameInvT (hsame_refl x)) (invCongr sameInvT)
    exact hsame_trans (mulCongr conjugateToEmpty (hsame_refl a))
      (hsame_trans (emptyNormalizer.right x centralX)
        (mulCongr (hsame_refl a) (hsame_symm conjugateToEmpty)))

def QuotientGroupSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def QuotientGroupSingletonClassifier (h k : BHist) : Prop :=
  QuotientGroupSingletonCarrier h ∧ QuotientGroupSingletonCarrier k ∧ hsame h k

theorem QuotientGroupSingleton_semanticNameCert :
    SemanticNameCert QuotientGroupSingletonCarrier QuotientGroupSingletonCarrier
      QuotientGroupSingletonCarrier QuotientGroupSingletonClassifier := by
  have emptyCarrier : QuotientGroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left
            (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

theorem QuotientGroupSingletonClassifier_visible_endpoint_absurd {p q k : BHist} :
    (QuotientGroupSingletonClassifier (BHist.e0 p) k -> False) ∧
      (QuotientGroupSingletonClassifier (BHist.e1 p) k -> False) ∧
        (QuotientGroupSingletonClassifier k (BHist.e0 q) -> False) ∧
          (QuotientGroupSingletonClassifier k (BHist.e1 q) -> False) := by
  constructor
  · intro classified
    exact not_hsame_e0_empty classified.left
  · constructor
    · intro classified
      exact not_hsame_e1_empty classified.left
    · constructor
      · intro classified
        exact not_hsame_e0_empty classified.right.left
      · intro classified
        exact not_hsame_e1_empty classified.right.left

def CentralizerCosetCarrier (mul : BHist -> BHist -> BHist) (a repr h : BHist) : Prop :=
  SubgroupCentralizerCarrier mul a repr ∧ hsame h repr

def CentralizerCosetClassifier (mul : BHist -> BHist -> BHist) (a repr h k : BHist) : Prop :=
  CentralizerCosetCarrier mul a repr h ∧ CentralizerCosetCarrier mul a repr k ∧ hsame h k

theorem CentralizerCoset_semanticNameCert {mul : BHist -> BHist -> BHist} {a repr : BHist}
    (reprCentral : SubgroupCentralizerCarrier mul a repr) :
    SemanticNameCert (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetCarrier mul a repr) (CentralizerCosetCarrier mul a repr)
      (CentralizerCosetClassifier mul a repr) := by
  constructor
  · constructor
    · exact Exists.intro repr (And.intro reprCentral (hsame_refl repr))
    · intro h carrier
      exact And.intro carrier (And.intro carrier (hsame_refl h))
    · intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    · intro h k classified _carrierH
      exact classified.right.left
  · intro h carrier
    exact carrier
  · intro h carrier
    exact carrier

theorem QuotientGroupCentralizerNormalizer_orbit_kernel_equivalence_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    {a x y : BHist} :
    let QuotientClassifier := fun p q : BHist =>
      SubgroupCentralizerNormalizer mul inv a p ∧
        SubgroupCentralizerNormalizer mul inv a q ∧
          Exists (fun z : BHist => SubgroupCentralizerCarrier mul a z ∧ hsame q (mul p z))
    QuotientClassifier x y <-> SubgroupCentralizerQuotientKernel mul inv a x y := by
  dsimp
  have rightInv : forall t : BHist, hsame (mul t (inv t)) BHist.Empty := by
    intro t
    have sameT :
        hsame t (mul (inv (inv t)) BHist.Empty) := by
      exact hsame_trans (hsame_symm (leftId t))
        (hsame_trans (mulCongr (hsame_symm (leftInv (inv t))) (hsame_refl t))
          (hsame_trans (assocC (inv (inv t)) (inv t) t)
            (mulCongr (hsame_refl (inv (inv t))) (leftInv t))))
    exact hsame_trans (mulCongr sameT (hsame_refl (inv t)))
      (hsame_trans (assocC (inv (inv t)) BHist.Empty (inv t))
        (hsame_trans (mulCongr (hsame_refl (inv (inv t))) (leftId (inv t)))
          (leftInv (inv t))))
  constructor
  · intro classified
    cases classified.right.right with
    | intro z witness =>
        have sameKernelZ : hsame (mul (inv x) y) z :=
          hsame_trans (mulCongr (hsame_refl (inv x)) witness.right)
            (BEDC.Derived.GroupUp.group_mul_left_inverse_cancel
              assocC leftId mulCongr leftInv x z)
        have kernelCentral :
            SubgroupCentralizerCarrier mul a (mul (inv x) y) :=
          hsame_trans (mulCongr sameKernelZ (hsame_refl a))
            (hsame_trans witness.left (mulCongr (hsame_refl a) (hsame_symm sameKernelZ)))
        exact And.intro classified.left (And.intro classified.right.left kernelCentral)
  · intro kernel
    have endpoint :
        hsame y (mul x (mul (inv x) y)) := by
      have forward :
          hsame (mul x (mul (inv x) y)) y :=
        hsame_trans (hsame_symm (assocC x (inv x) y))
          (hsame_trans (mulCongr (rightInv x) (hsame_refl y)) (leftId y))
      exact hsame_symm forward
    exact And.intro kernel.left
      (And.intro kernel.right.left
        (Exists.intro (mul (inv x) y) (And.intro kernel.right.right endpoint)))

theorem QuotientGroupCentralizerNormalizer_identity_fiber_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    let QuotientClassifier := fun p q : BHist =>
      SubgroupCentralizerNormalizer mul inv a p ∧
        SubgroupCentralizerNormalizer mul inv a q ∧
          Exists (fun z : BHist => SubgroupCentralizerCarrier mul a z ∧
            hsame q (mul p z))
    (QuotientClassifier BHist.Empty x <-> SubgroupCentralizerCarrier mul a x) ∧
      (QuotientClassifier x BHist.Empty <-> SubgroupCentralizerCarrier mul a x) := by
  dsimp
  have leftClassifierKernel :
      (SubgroupCentralizerNormalizer mul inv a BHist.Empty ∧
          SubgroupCentralizerNormalizer mul inv a x ∧
            Exists (fun z : BHist => SubgroupCentralizerCarrier mul a z ∧
              hsame x (mul BHist.Empty z))) <->
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x :=
    QuotientGroupCentralizerNormalizer_orbit_kernel_equivalence_iff
      assocC leftId mulCongr leftInv
  have rightClassifierKernel :
      (SubgroupCentralizerNormalizer mul inv a x ∧
          SubgroupCentralizerNormalizer mul inv a BHist.Empty ∧
            Exists (fun z : BHist => SubgroupCentralizerCarrier mul a z ∧
              hsame BHist.Empty (mul x z))) <->
        SubgroupCentralizerQuotientKernel mul inv a x BHist.Empty :=
    QuotientGroupCentralizerNormalizer_orbit_kernel_equivalence_iff
      assocC leftId mulCongr leftInv
  have leftKernelFiber :
      SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x <->
        SubgroupCentralizerCarrier mul a x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have rightKernelFiber :
      SubgroupCentralizerQuotientKernel mul inv a x BHist.Empty <->
        SubgroupCentralizerCarrier mul a x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_right_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  constructor
  · constructor
    · intro classified
      exact Iff.mp leftKernelFiber (Iff.mp leftClassifierKernel classified)
    · intro centralX
      exact Iff.mpr leftClassifierKernel (Iff.mpr leftKernelFiber centralX)
  · constructor
    · intro classified
      exact Iff.mp rightKernelFiber (Iff.mp rightClassifierKernel classified)
    · intro centralX
      exact Iff.mpr rightClassifierKernel (Iff.mpr rightKernelFiber centralX)

theorem QuotientGroupCentralizerNormalizer_identity_fiber_subgroup_package
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    let KQ := fun x : BHist =>
      SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x
    KQ BHist.Empty ∧
      (forall {x y : BHist}, KQ x -> KQ y -> KQ (mul x y)) ∧
      (forall {x : BHist}, KQ x -> KQ (inv x)) ∧
      (forall {x y : BHist}, KQ x -> hsame x y -> KQ y) ∧
      (forall x : BHist, KQ x <-> SubgroupCentralizerCarrier mul a x) := by
  dsimp
  have rows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have fiber :
      forall x : BHist,
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x <->
          SubgroupCentralizerCarrier mul a x := by
    intro x
    exact BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have emptyKQ : SubgroupCentralizerQuotientKernel mul inv a BHist.Empty BHist.Empty :=
    Iff.mpr (fiber BHist.Empty) rows.right.left
  have mulClosed :
      forall {x y : BHist},
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x ->
          SubgroupCentralizerQuotientKernel mul inv a BHist.Empty y ->
            SubgroupCentralizerQuotientKernel mul inv a BHist.Empty (mul x y) := by
    intro x y kernelX kernelY
    exact Iff.mpr (fiber (mul x y))
      (rows.right.right.left (Iff.mp (fiber x) kernelX) (Iff.mp (fiber y) kernelY))
  have invClosed :
      forall {x : BHist},
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x ->
          SubgroupCentralizerQuotientKernel mul inv a BHist.Empty (inv x) := by
    intro x kernelX
    exact Iff.mpr (fiber (inv x)) (rows.right.right.right.left (Iff.mp (fiber x) kernelX))
  have hsameClosed :
      forall {x y : BHist},
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x ->
          hsame x y -> SubgroupCentralizerQuotientKernel mul inv a BHist.Empty y := by
    intro x y kernelX sameXY
    exact Iff.mpr (fiber y)
      (rows.right.right.right.right (Iff.mp (fiber x) kernelX) sameXY)
  exact And.intro emptyKQ
    (And.intro mulClosed (And.intro invClosed (And.intro hsameClosed fiber)))

end BEDC.Derived.QuotientGroupUp
