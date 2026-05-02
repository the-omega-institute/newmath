import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.Derived.GroupUp
import BEDC.Derived.RingUp
import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def FieldSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FieldSingletonClassifier (h k : BHist) : Prop :=
  FieldSingletonCarrier h ∧ FieldSingletonCarrier k ∧ hsame h k

theorem FieldSingletonClassifier_append_context_cancel_iff {L R Q S : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R ->
      (FieldSingletonClassifier (append L Q) (append R S) <->
        FieldSingletonClassifier Q S) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.right (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
  · intro classified
    have leftCarrier : FieldSingletonCarrier (append L Q) :=
      append_eq_empty_iff.mpr (And.intro carrierL classified.left)
    have rightCarrier : FieldSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro carrierR classified.right.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

def FieldSingletonAdd (_x _y : BHist) : BHist :=
  BHist.Empty

def FieldSingletonNeg (_x : BHist) : BHist :=
  BHist.Empty

def FieldSingletonZero : BHist :=
  BHist.Empty

def FieldSingletonMul (_x _y : BHist) : BHist :=
  BHist.Empty

def FieldSingletonOne : BHist :=
  BHist.Empty

def FieldSingletonNonZero (a : BHist) : Prop :=
  FieldSingletonCarrier a ∧ hsame a (BHist.e0 BHist.Empty)

def FieldSingletonInv (a : BHist) (_p : FieldSingletonNonZero a) : BHist :=
  BHist.Empty

theorem singleton_empty_history_field_schema_laws :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
      FieldSingletonClassifier ∧
      (∀ {a : BHist}, FieldSingletonCarrier a → FieldSingletonNonZero a → False) ∧
      (∀ {a b : BHist}, FieldSingletonClassifier a b → FieldSingletonNonZero a →
        FieldSingletonNonZero b) ∧
      (∀ {a : BHist} (p : FieldSingletonNonZero a),
        FieldSingletonCarrier (FieldSingletonInv a p)) ∧
      (∀ {a b : BHist} (p : FieldSingletonNonZero a) (q : FieldSingletonNonZero b),
        FieldSingletonClassifier a b →
          FieldSingletonClassifier (FieldSingletonInv a p) (FieldSingletonInv b q)) ∧
      (∀ {a : BHist} (p : FieldSingletonNonZero a),
        FieldSingletonClassifier (FieldSingletonMul (FieldSingletonInv a p) a)
          FieldSingletonOne) ∧
      (∀ {a : BHist} (p : FieldSingletonNonZero a),
        FieldSingletonClassifier (FieldSingletonMul a (FieldSingletonInv a p))
          FieldSingletonOne) := by
  have emptyCarrier : FieldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact {
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
  · constructor
    · intro a carrierA nonzeroA
      exact not_hsame_emp_e0 (hsame_trans (hsame_symm carrierA) nonzeroA.right)
    · constructor
      · intro a b sameAB nonzeroA
        exact And.intro sameAB.right.left (hsame_trans (hsame_symm sameAB.right.right) nonzeroA.right)
      · constructor
        · intro a p
          exact emptyCarrier
        · constructor
          · intro a b p q _sameAB
            exact emptyClassified
          · constructor
            · intro a p
              exact emptyClassified
            · intro a p
              exact emptyClassified

theorem field_inverse_congruence_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (sameAB : hsame a b) (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) := by
  have transportedLeft : hsame (mul (inv a p) b) one := by
    exact hsame_trans
      (hsame_symm (mulCongr (hsame_refl (inv a p)) sameAB))
      (leftInv a p)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    transportedLeft
    (rightInv b q)

theorem field_inverse_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) -> hsame a b := by
  intro sameInv
  have transportedLeft : hsame (mul (inv b q) a) one := by
    exact hsame_trans
      (hsame_symm (mulCongr sameInv (hsame_refl a)))
      (leftInv a p)
  exact hsame_symm
    (BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC
      leftId
      rightId
      mulCongr
      (rightInv b q)
      transportedLeft)

theorem field_inverse_nonzero_from_one_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeft : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    {a : BHist} (pa : NonZero a) : NonZero (inv a pa) := by
  apply nonzeroOfApartEmpty
  intro inverseEmpty
  have productEmpty : hsame (mul (inv a pa) a) BHist.Empty := by
    exact hsame_trans (mulCongr inverseEmpty (hsame_refl a)) (zeroLeft a)
  exact oneApartEmpty (hsame_trans (hsame_symm (leftInv a pa)) productEmpty)

 theorem field_inverse_product_reverse_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
  have reverseRight : hsame (mul (mul a b) (mul (inv b pb) (inv a pa))) one := by
    have inner :
        hsame (mul b (mul (inv b pb) (inv a pa))) (inv a pa) := by
      exact hsame_trans (hsame_symm (assocC b (inv b pb) (inv a pa)))
        (hsame_trans (mulCongr (rightInv b pb) (hsame_refl (inv a pa)))
          (leftId (inv a pa)))
    exact hsame_trans (assocC a b (mul (inv b pb) (inv a pa)))
      (hsame_trans (mulCongr (hsame_refl a) inner) (rightInv a pa))
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    (leftInv (mul a b) pab)
    reverseRight

 theorem field_mul_inverse_right_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one) :
    forall (a b : BHist) (pb : NonZero b),
      hsame (mul (mul a b) (inv b pb)) a := by
  intro a b pb
  have reassoc :
      hsame (mul (mul a b) (inv b pb)) (mul a (mul b (inv b pb))) := by
    exact assocC a b (inv b pb)
  have cancelTail : hsame (mul a (mul b (inv b pb))) (mul a one) := by
    exact mulCongr (hsame_refl a) (rightInv b pb)
  exact hsame_trans reassoc (hsame_trans cancelTail (rightId a))

 theorem field_right_mul_equation_solution_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b a : BHist} (pb : NonZero b) :
    hsame (mul x b) a -> hsame x (mul a (inv b pb)) := by
  intro sameProduct
  exact hsame_trans
    (hsame_symm
      (field_mul_inverse_right_cancel_from_apartness assocC rightId mulCongr rightInv x b pb))
    (mulCongr sameProduct (hsame_refl (inv b pb)))

 theorem field_right_mul_equation_solution_from_apartness_iff {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b a : BHist} (pb : NonZero b) :
    hsame (mul x b) a <-> hsame x (mul a (inv b pb)) := by
  constructor
  · intro sameProduct
    exact field_right_mul_equation_solution_from_apartness
      assocC rightId mulCongr rightInv pb sameProduct
  · intro sameSolution
    have transported :
        hsame (mul x b) (mul (mul a (inv b pb)) b) := by
      exact mulCongr sameSolution (hsame_refl b)
    have reassoc :
        hsame (mul (mul a (inv b pb)) b) (mul a (mul (inv b pb) b)) := by
      exact assocC a (inv b pb) b
    have cancelTail :
        hsame (mul a (mul (inv b pb) b)) (mul a one) := by
      exact mulCongr (hsame_refl a) (leftInv b pb)
    exact hsame_trans transported
      (hsame_trans reassoc (hsame_trans cancelTail (rightId a)))

 theorem field_right_mul_equation_exact_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {x b a : BHist} (pb : NonZero b) :
    (hsame (mul x b) a ↔ hsame x (mul a (inv b pb))) := by
  exact field_right_mul_equation_solution_from_apartness_iff
    assocC rightId mulCongr leftInv rightInv pb

 theorem field_mul_inverse_left_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one) :
    forall (a b : BHist) (pa : NonZero a),
      hsame (mul (inv a pa) (mul a b)) b := by
  intro a b pa
  have reassoc :
      hsame (mul (inv a pa) (mul a b)) (mul (mul (inv a pa) a) b) := by
    exact hsame_symm (assocC (inv a pa) a b)
  have cancelHead : hsame (mul (mul (inv a pa) a) b) (mul one b) := by
    exact mulCongr (leftInv a pa) (hsame_refl b)
  exact hsame_trans reassoc (hsame_trans cancelHead (leftId b))

 theorem field_middle_mul_equation_solution_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x b c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) c -> hsame x (mul (inv a pa) (mul c (inv b pb))) := by
  intro sameProduct
  have solveRight : hsame (mul a x) (mul c (inv b pb)) := by
    exact field_right_mul_equation_solution_from_apartness
      assocC rightId mulCongr rightInv pb sameProduct
  exact hsame_trans
    (hsame_symm (field_mul_inverse_left_cancel_from_apartness
      assocC leftId mulCongr leftInv a x pa))
    (mulCongr (hsame_refl (inv a pa)) solveRight)

 theorem field_middle_mul_equation_exact_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x b c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) c <->
      hsame x (mul (inv a pa) (mul c (inv b pb))) := by
  constructor
  · intro sameProduct
    exact field_middle_mul_equation_solution_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pb sameProduct
  · intro sameSolution
    have cancelLeft :
        hsame (mul a x) (mul c (inv b pb)) := by
      have replaceX :
          hsame (mul a x) (mul a (mul (inv a pa) (mul c (inv b pb)))) := by
        exact mulCongr (hsame_refl a) sameSolution
      have cancelA :
          hsame (mul a (mul (inv a pa) (mul c (inv b pb)))) (mul c (inv b pb)) := by
        exact hsame_trans (hsame_symm (assocC a (inv a pa) (mul c (inv b pb))))
          (hsame_trans (mulCongr (rightInv a pa) (hsame_refl (mul c (inv b pb))))
            (leftId (mul c (inv b pb))))
      exact hsame_trans replaceX cancelA
    have replaceLeft :
        hsame (mul (mul a x) b) (mul (mul c (inv b pb)) b) := by
      exact mulCongr cancelLeft (hsame_refl b)
    have cancelRight :
        hsame (mul (mul c (inv b pb)) b) c := by
      exact hsame_trans (assocC c (inv b pb) b)
        (hsame_trans (mulCongr (hsame_refl c) (leftInv b pb)) (rightId c))
    exact hsame_trans replaceLeft cancelRight

 theorem field_middle_mul_equation_solution_from_apartness_iff {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x b c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) c <->
      hsame x (mul (inv a pa) (mul c (inv b pb))) := by
  exact field_middle_mul_equation_exact_from_apartness
    assocC leftId rightId mulCongr leftInv rightInv pa pb

 theorem field_left_mul_equation_exact_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a x c : BHist} (pa : NonZero a) :
    hsame (mul a x) c ↔ hsame x (mul (inv a pa) c) := by
  constructor
  · intro sameProduct
    have cancelLeft :
        hsame (mul (inv a pa) (mul a x)) x := by
      exact field_mul_inverse_left_cancel_from_apartness
        assocC leftId mulCongr leftInv a x pa
    have transported :
        hsame (mul (inv a pa) (mul a x)) (mul (inv a pa) c) := by
      exact mulCongr (hsame_refl (inv a pa)) sameProduct
    exact hsame_trans (hsame_symm cancelLeft) transported
  · intro sameSolution
    have transported :
        hsame (mul a x) (mul a (mul (inv a pa) c)) := by
      exact mulCongr (hsame_refl a) sameSolution
    have reassoc :
        hsame (mul a (mul (inv a pa) c)) (mul (mul a (inv a pa)) c) := by
      exact hsame_symm (assocC a (inv a pa) c)
    have cancelHead :
        hsame (mul (mul a (inv a pa)) c) (mul one c) := by
      exact mulCongr (rightInv a pa) (hsame_refl c)
    exact hsame_trans transported
      (hsame_trans reassoc (hsame_trans cancelHead (leftId c)))

 theorem field_two_sided_mul_exact_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y : BHist} (pa : NonZero a) (pb : NonZero b) :
    (hsame (mul (mul a x) b) (mul (mul a y) b) <-> hsame x y) := by
  constructor
  · intro sameProducts
    have rightTransport :
        hsame (mul (mul (mul a x) b) (inv b pb))
          (mul (mul (mul a y) b) (inv b pb)) := by
      exact mulCongr sameProducts (hsame_refl (inv b pb))
    have cancelRightLeft :
        hsame (mul (mul (mul a x) b) (inv b pb)) (mul a x) := by
      exact field_mul_inverse_right_cancel_from_apartness
        assocC rightId mulCongr rightInv (mul a x) b pb
    have cancelRightRight :
        hsame (mul (mul (mul a y) b) (inv b pb)) (mul a y) := by
      exact field_mul_inverse_right_cancel_from_apartness
        assocC rightId mulCongr rightInv (mul a y) b pb
    have cancelRight : hsame (mul a x) (mul a y) := by
      exact hsame_trans (hsame_symm cancelRightLeft)
        (hsame_trans rightTransport cancelRightRight)
    have leftTransport :
        hsame (mul (inv a pa) (mul a x)) (mul (inv a pa) (mul a y)) := by
      exact mulCongr (hsame_refl (inv a pa)) cancelRight
    have cancelLeftLeft :
        hsame (mul (inv a pa) (mul a x)) x := by
      exact field_mul_inverse_left_cancel_from_apartness
        assocC leftId mulCongr leftInv a x pa
    have cancelLeftRight :
        hsame (mul (inv a pa) (mul a y)) y := by
      exact field_mul_inverse_left_cancel_from_apartness
        assocC leftId mulCongr leftInv a y pa
    exact hsame_trans (hsame_symm cancelLeftLeft)
      (hsame_trans leftTransport cancelLeftRight)
  · intro sameMiddle
    exact mulCongr (mulCongr (hsame_refl a) sameMiddle) (hsame_refl b)

theorem field_singleton_nonzero_absurd {a : BHist} :
    hsame a BHist.Empty -> hsame a (BHist.e0 BHist.Empty) -> False := by
  intro sameEmpty sameSingleton
  exact not_hsame_emp_e0 (hsame_trans (hsame_symm sameEmpty) sameSingleton)

theorem FieldSingletonNonZero_empty_e0_forced {a : BHist} :
    FieldSingletonNonZero a -> hsame BHist.Empty (BHist.e0 BHist.Empty) := by
  intro nonzero
  exact hsame_trans (hsame_symm nonzero.left) nonzero.right

theorem FieldSingletonNonZero_absurd {h : BHist} : FieldSingletonNonZero h -> False := by
  intro nonzero
  exact field_singleton_nonzero_absurd nonzero.left nonzero.right

 theorem field_one_sided_zero_product_cancel_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {zero one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one) :
    forall a b : BHist,
      (NonZero a -> hsame (mul a b) zero -> hsame b zero) ∧
        (NonZero b -> hsame (mul a b) zero -> hsame a zero) := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
      addCongr mulCongr leftDistrib rightDistrib
  intro a b
  constructor
  · intro nonzeroA productZero
    have transportProduct :
        hsame (mul (inv a nonzeroA) (mul a b)) (mul (inv a nonzeroA) zero) := by
      exact mulCongr (hsame_refl (inv a nonzeroA)) productZero
    have cancelLeft :
        hsame (mul (inv a nonzeroA) (mul a b)) b := by
      exact field_mul_inverse_left_cancel_from_apartness
        assocC leftId mulCongr leftInv a b nonzeroA
    exact hsame_trans (hsame_symm cancelLeft)
      (hsame_trans transportProduct (zeroAbsorption.left (inv a nonzeroA)))
  · intro nonzeroB productZero
    have transportProduct :
        hsame (mul (mul a b) (inv b nonzeroB)) (mul zero (inv b nonzeroB)) := by
      exact mulCongr productZero (hsame_refl (inv b nonzeroB))
    have cancelRight :
        hsame (mul (mul a b) (inv b nonzeroB)) a := by
      exact field_mul_inverse_right_cancel_from_apartness
        assocC rightId mulCongr rightInv a b nonzeroB
    exact hsame_trans (hsame_symm cancelRight)
      (hsame_trans transportProduct (zeroAbsorption.right (inv b nonzeroB)))
 theorem field_two_sided_empty_product_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) BHist.Empty <-> hsame x BHist.Empty := by
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib
  have emptyProduct : hsame (mul (mul a BHist.Empty) b) BHist.Empty := by
    exact hsame_trans (mulCongr (zeroAbsorption.left a) (hsame_refl b))
      (zeroAbsorption.right b)
  have exactProducts : hsame (mul (mul a x) b) (mul (mul a BHist.Empty) b) <->
        hsame x BHist.Empty :=
    field_two_sided_mul_exact_from_apartness assocC leftId rightId mulCongr leftInv
      rightInv pa pb
  constructor
  · intro productEmpty
    exact Iff.mp exactProducts (hsame_trans productEmpty (hsame_symm emptyProduct))
  · intro xEmpty
    exact hsame_trans (Iff.mpr exactProducts xEmpty) emptyProduct
 theorem field_nonzero_factors_exclude_empty_product
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul a b) BHist.Empty -> False := by
  intro productEmpty
  have bEmpty : hsame b BHist.Empty := by
    exact (field_one_sided_zero_product_cancel_from_apartness addAssoc zeroLeft negLeft
      assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv a b).left
      pa productEmpty
  exact nonzeroEmptyAbsurd (nonzeroTransport bEmpty pb)

theorem field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff {u : BHist} :
    ((∀ {d r : BHist}, RatHistoryCarrier d -> Cont u d r -> RatHistoryClassifier r d) ↔
      hsame u BHist.Empty) := by
  constructor
  · intro leftUnit
    have carrierD1 : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
      RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
    have canonicalContinuation :
        Cont u (BHist.e1 BHist.Empty) (append u (BHist.e1 BHist.Empty)) :=
      cont_intro rfl
    have classifiedResult :
        RatHistoryClassifier (append u (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty) :=
      leftUnit carrierD1 canonicalContinuation
    have collapsedContinuation : Cont u (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
      cont_result_hsame_transport canonicalContinuation classifiedResult.right.right
    exact cont_left_unit_unique collapsedContinuation
  · intro uEmpty
    intro d r carrierD contUDR
    have sameRD : hsame r d := by
      cases uEmpty
      exact cont_left_unit_result contUDR
    exact ⟨RatHistoryCarrier_hsame_transport (hsame_symm sameRD) carrierD,
      carrierD, sameRD⟩

theorem fieldSingletonEmptyNonZero_append_right_cancel_iff {P Q : BHist} :
    fieldSingletonEmptyCarrier P ->
      (fieldSingletonEmptyNonZero (append Q P) ↔ fieldSingletonEmptyNonZero Q) := by
  intro carrierP
  constructor
  · intro nonzeroAppend classifiedQ
    apply nonzeroAppend
    have leftCarrier : fieldSingletonEmptyCarrier (append Q P) :=
      append_eq_empty_iff.mpr (And.intro classifiedQ.left carrierP)
    exact And.intro leftCarrier (And.intro (hsame_refl BHist.Empty) leftCarrier)
  · intro nonzeroQ classifiedAppend
    apply nonzeroQ
    have split := append_eq_empty_iff.mp classifiedAppend.left
    exact And.intro split.left (And.intro (hsame_refl BHist.Empty) split.left)

theorem fieldSingletonEmptyNonZero_append_left_cancel_iff {P Q : BHist} :
    fieldSingletonEmptyCarrier P ->
      (fieldSingletonEmptyNonZero (append P Q) ↔ fieldSingletonEmptyNonZero Q) := by
  intro carrierP
  constructor
  · intro nonzeroAppend classifiedQ
    apply nonzeroAppend
    have leftCarrier : fieldSingletonEmptyCarrier (append P Q) :=
      append_eq_empty_iff.mpr (And.intro carrierP classifiedQ.left)
    exact And.intro leftCarrier (And.intro (hsame_refl BHist.Empty) leftCarrier)
  · intro nonzeroQ classifiedAppend
    apply nonzeroQ
    have split := append_eq_empty_iff.mp classifiedAppend.left
    exact And.intro split.right (And.intro (hsame_refl BHist.Empty) split.right)

end BEDC.Derived.FieldUp
