import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def FieldSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def FieldSingletonClassifier (h k : BHist) : Prop :=
  FieldSingletonCarrier h ∧ FieldSingletonCarrier k ∧ hsame h k

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

def fieldSingletonEmptyCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def fieldSingletonEmptyClassifier (h k : BHist) : Prop :=
  fieldSingletonEmptyCarrier h ∧ fieldSingletonEmptyCarrier k ∧ hsame h k

def fieldSingletonEmptyNonZero (h : BHist) : Prop :=
  fieldSingletonEmptyClassifier h BHist.Empty -> False

def fieldSingletonEmptyMul (_x _y : BHist) : BHist :=
  BHist.Empty

def fieldSingletonEmptyOne : BHist :=
  BHist.Empty

def fieldSingletonEmptyInv (_h : BHist) (_p : fieldSingletonEmptyNonZero _h) : BHist :=
  BHist.Empty

theorem field_singleton_empty_schema_laws :
    (fieldSingletonEmptyCarrier BHist.Empty) ∧
      (fieldSingletonEmptyNonZero BHist.Empty -> False) ∧
      (∀ {h k : BHist}, fieldSingletonEmptyClassifier h k ->
        fieldSingletonEmptyNonZero h -> fieldSingletonEmptyNonZero k) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h), fieldSingletonEmptyCarrier h ->
        fieldSingletonEmptyCarrier (fieldSingletonEmptyInv h p)) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h),
        fieldSingletonEmptyClassifier (fieldSingletonEmptyMul (fieldSingletonEmptyInv h p) h)
          fieldSingletonEmptyOne) ∧
      (∀ (h : BHist) (p : fieldSingletonEmptyNonZero h),
        fieldSingletonEmptyClassifier (fieldSingletonEmptyMul h (fieldSingletonEmptyInv h p))
          fieldSingletonEmptyOne) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro nonzeroEmpty
      apply nonzeroEmpty
      constructor
      · exact hsame_refl BHist.Empty
      · constructor
        · exact hsame_refl BHist.Empty
        · exact hsame_refl BHist.Empty
    · constructor
      · intro h k sameHK nonzeroH
        intro sameKEmpty
        apply nonzeroH
        constructor
        · exact sameHK.left
        · constructor
          · exact hsame_refl BHist.Empty
          · exact hsame_trans sameHK.right.right sameKEmpty.right.right
      · constructor
        · intro h p carrierH
          exact hsame_refl BHist.Empty
        · constructor
          · intro h p
            constructor
            · exact hsame_refl BHist.Empty
            · constructor
              · exact hsame_refl BHist.Empty
              · exact hsame_refl BHist.Empty
          · intro h p
            constructor
            · exact hsame_refl BHist.Empty
            · constructor
              · exact hsame_refl BHist.Empty
              · exact hsame_refl BHist.Empty

end BEDC.Derived.FieldUp
