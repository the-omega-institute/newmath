import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.EulerBooleSummation

abbrev binom (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

structure QRat where
  num : Int
  denPred : Nat

namespace QRat

def den (q : QRat) : Nat :=
  Nat.succ q.denPred

def ofInt (z : Int) : QRat :=
  { num := z, denPred := 0 }

def ofNat (n : Nat) : QRat :=
  ofInt n

def zero : QRat :=
  ofInt 0

def one : QRat :=
  ofInt 1

def neg (q : QRat) : QRat :=
  { num := -q.num, denPred := q.denPred }

def add (q r : QRat) : QRat :=
  { num := q.num * Int.ofNat r.den + r.num * Int.ofNat q.den
    denPred := q.den * r.den - 1 }

def sub (q r : QRat) : QRat :=
  add q (neg r)

def mul (q r : QRat) : QRat :=
  { num := q.num * r.num
    denPred := q.den * r.den - 1 }

def inv (q : QRat) : QRat :=
  match q.num with
  | Int.ofNat 0 => zero
  | Int.ofNat (Nat.succ n) =>
      { num := Int.ofNat q.den, denPred := n }
  | Int.negSucc n =>
      { num := -Int.ofNat q.den, denPred := n }

def div (q r : QRat) : QRat :=
  mul q (inv r)

def pow (q : QRat) : Nat -> QRat
  | 0 => one
  | Nat.succ n => mul (pow q n) q

def alt (n : Nat) : QRat :=
  match n % 2 with
  | 0 => one
  | _ => neg one

def readback (q : QRat) : Rat :=
  Int.cast q.num / Nat.cast q.den

theorem zero_num :
    zero.num = 0 := by
  rfl

theorem one_num :
    one.num = 1 := by
  rfl

theorem neg_num (q : QRat) :
    (neg q).num = -q.num := by
  rfl

theorem add_num (q r : QRat) :
    (add q r).num = q.num * Int.ofNat r.den + r.num * Int.ofNat q.den := by
  rfl

theorem mul_num (q r : QRat) :
    (mul q r).num = q.num * r.num := by
  rfl

theorem div_def (q r : QRat) :
    div q r = mul q (inv r) := by
  rfl

end QRat

def natFactorial : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * natFactorial n

def oddIndex (j : Nat) : Nat :=
  match j with
  | 0 => 1
  | Nat.succ j => Nat.succ (Nat.succ (oddIndex j))

def evenIndex (j : Nat) : Nat :=
  match j with
  | 0 => 0
  | Nat.succ j => Nat.succ (Nat.succ (evenIndex j))

def parityEven : Nat -> Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (Nat.succ n) => parityEven n

def halfIndex : Nat -> Nat
  | 0 => 0
  | Nat.succ 0 => 0
  | Nat.succ (Nat.succ n) => Nat.succ (halfIndex n)

theorem parityEven_evenIndex (j : Nat) :
    parityEven (evenIndex j) = true := by
  induction j with
  | zero =>
      rfl
  | succ _ ih =>
      exact ih

theorem parityEven_oddIndex (j : Nat) :
    parityEven (oddIndex j) = false := by
  induction j with
  | zero =>
      rfl
  | succ _ ih =>
      exact ih

theorem halfIndex_evenIndex (j : Nat) :
    halfIndex (evenIndex j) = j := by
  induction j with
  | zero =>
      rfl
  | succ _ ih =>
      change Nat.succ (halfIndex (evenIndex _)) = Nat.succ _
      exact congrArg Nat.succ ih

theorem halfIndex_oddIndex (j : Nat) :
    halfIndex (oddIndex j) = j := by
  induction j with
  | zero =>
      rfl
  | succ _ ih =>
      change Nat.succ (halfIndex (oddIndex _)) = Nat.succ _
      exact congrArg Nat.succ ih

def oddContributionFromList (degree idx : Nat) : List QRat -> QRat
  | [] => QRat.zero
  | coeff :: coeffs =>
      QRat.add
        (QRat.mul (QRat.ofNat (binom degree (oddIndex idx))) coeff)
        (oddContributionFromList degree (Nat.succ idx) coeffs)

def nextOddFromPrefix (coeffs : List QRat) (j : Nat) : QRat :=
  QRat.neg
    (QRat.div
      (QRat.add QRat.one
        (oddContributionFromList (oddIndex (Nat.succ j)) 0 coeffs))
      (QRat.ofNat 2))

def oddPrefix : Nat -> List QRat
  | 0 =>
      [QRat.neg (QRat.div QRat.one (QRat.ofNat 2))]
  | Nat.succ j =>
      let prior := oddPrefix j
      prior ++ [nextOddFromPrefix prior j]

def listLast (fallback : QRat) : List QRat -> QRat
  | [] => fallback
  | x :: [] => x
  | _ :: y :: ys => listLast fallback (y :: ys)

theorem listLast_append_single (fallback x : QRat) (xs : List QRat) :
    listLast fallback (xs ++ [x]) = x := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases xs with
      | nil =>
          rfl
      | cons b bs =>
          exact ih

def eulerOdd (j : Nat) : QRat :=
  listLast QRat.zero (oddPrefix j)

def eulerEven : Nat -> QRat
  | 0 => QRat.one
  | Nat.succ _ => QRat.zero

def eulerBase (n : Nat) : QRat :=
  match parityEven n with
  | true => eulerEven (halfIndex n)
  | false => eulerOdd (halfIndex n)

def eulerPolynomialAtAux (degree : Nat) (x : QRat) : Nat -> QRat
  | 0 =>
      QRat.mul
        (QRat.mul (QRat.ofNat (binom degree 0)) (eulerBase degree))
        (QRat.pow x 0)
  | Nat.succ j =>
      QRat.add
        (eulerPolynomialAtAux degree x j)
        (QRat.mul
          (QRat.mul
            (QRat.ofNat (binom degree (Nat.succ j)))
            (eulerBase (degree - Nat.succ j)))
          (QRat.pow x (Nat.succ j)))

def eulerPolynomialAt (degree : Nat) (x : QRat) : QRat :=
  eulerPolynomialAtAux degree x degree

theorem eulerBase_zero :
    eulerBase 0 = QRat.one := by
  rfl

theorem eulerBase_zero_value :
    eulerBase 0 = { num := 1, denPred := 0 } := by
  rfl

theorem eulerBase_one_shape :
    eulerBase 1 =
      QRat.neg (QRat.div QRat.one (QRat.ofNat 2)) := by
  rfl

theorem eulerBase_one_value :
    eulerBase 1 = { num := -1, denPred := 1 } := by
  rfl

theorem eulerBase_two_shape :
    eulerBase 2 = QRat.zero := by
  rfl

theorem eulerPolynomialAt_zero :
    eulerPolynomialAt 0 QRat.zero =
      QRat.mul
        (QRat.mul (QRat.ofNat (binom 0 0)) (eulerBase 0))
        (QRat.pow QRat.zero 0) := by
  rfl

theorem eulerEvenPositiveShape (j : Nat) :
    eulerEven (Nat.succ j) = QRat.zero := by
  rfl

theorem eulerBase_even_positive_zero (j : Nat) :
    eulerBase (evenIndex (Nat.succ j)) = QRat.zero := by
  unfold eulerBase
  rw [parityEven_evenIndex, halfIndex_evenIndex]
  rfl

theorem eulerBase_odd_succ_recurrence (j : Nat) :
    eulerBase (oddIndex (Nat.succ j)) =
      nextOddFromPrefix (oddPrefix j) j := by
  unfold eulerBase eulerOdd
  rw [parityEven_oddIndex, halfIndex_oddIndex]
  change
    listLast QRat.zero
      (let prior := oddPrefix j
       prior ++ [nextOddFromPrefix prior j]) =
    nextOddFromPrefix (oddPrefix j) j
  exact listLast_append_single QRat.zero
    (nextOddFromPrefix (oddPrefix j) j) (oddPrefix j)

theorem eulerBase_initial_and_parity_recurrence :
    eulerBase 0 = QRat.one ∧
      eulerBase 1 = QRat.neg (QRat.div QRat.one (QRat.ofNat 2)) ∧
        (∀ j : Nat, eulerBase (evenIndex (Nat.succ j)) = QRat.zero) ∧
          (∀ j : Nat,
            eulerBase (oddIndex (Nat.succ j)) =
              nextOddFromPrefix (oddPrefix j) j) := by
  exact ⟨eulerBase_zero, eulerBase_one_shape,
    eulerBase_even_positive_zero, eulerBase_odd_succ_recurrence⟩

class AdditiveCarrier (A : Type u) where
  zero : A
  add : A -> A -> A
  neg : A -> A
  scale : QRat -> A -> A
  eqv : A -> A -> Prop
  refl : forall x : A, eqv x x
  symm : forall {x y : A}, eqv x y -> eqv y x
  trans : forall {x y z : A}, eqv x y -> eqv y z -> eqv x z
  add_congr :
    forall {x x' y y' : A}, eqv x x' -> eqv y y' ->
      eqv (add x y) (add x' y')
  neg_congr :
    forall {x y : A}, eqv x y -> eqv (neg x) (neg y)
  scale_congr :
    forall (q : QRat) {x y : A}, eqv x y -> eqv (scale q x) (scale q y)
  add_assoc : forall x y z : A, eqv (add (add x y) z) (add x (add y z))
  add_comm : forall x y : A, eqv (add x y) (add y x)
  add_zero : forall x : A, eqv (add x zero) x
  zero_add : forall x : A, eqv (add zero x) x
  add_neg : forall x : A, eqv (add x (neg x)) zero
  neg_add : forall x : A, eqv (add (neg x) x) zero

namespace AdditiveCarrier

variable {A : Type u} (C : AdditiveCarrier A)

abbrev sub (x y : A) : A :=
  C.add x (C.neg y)

def alternatingPositive : Nat -> Bool
  | 0 => true
  | Nat.succ n =>
      match alternatingPositive n with
      | true => false
      | false => true

def signed (n : Nat) (x : A) : A :=
  match alternatingPositive n with
  | true => x
  | false => C.neg x

def rangeSum (start len : Nat) (f : Nat -> A) : A :=
  match len with
  | 0 => C.zero
  | Nat.succ len' => C.add (f start) (rangeSum (Nat.succ start) len' f)

def alternatingRangeSum (start len : Nat) (f : Nat -> A) : A :=
  rangeSum C start len (fun n => signed C n (f n))

def forwardDiff (f : Nat -> A) : Nat -> A :=
  fun n => sub C (f (Nat.succ n)) (f n)

def iteratedDiff : Nat -> (Nat -> A) -> Nat -> A
  | 0, f => f
  | Nat.succ k, f => forwardDiff C (iteratedDiff k f)

def rangeEnd (start len : Nat) : Nat :=
  match len with
  | 0 => start
  | Nat.succ len' => rangeEnd (Nat.succ start) len'

def endpointCoeff (order : Nat) : QRat :=
  QRat.div
    (eulerBase order)
    (QRat.ofNat (2 * natFactorial order))

def eulerPrimitive (order : Nat) (f : Nat -> A) (n : Nat) : A :=
  match order with
  | 0 => C.zero
  | Nat.succ order' =>
      C.add
        (C.scale (endpointCoeff order')
          (iteratedDiff C order' f n))
        (eulerPrimitive order' f n)

def endpointCorrection (start len order : Nat) (f : Nat -> A) : A :=
  sub C
    (signed C start (eulerPrimitive C order f start))
    (signed C (rangeEnd start len)
      (eulerPrimitive C order f (rangeEnd start len)))

def localBoundary (n order : Nat) (f : Nat -> A) : A :=
  sub C
    (signed C n (eulerPrimitive C order f n))
    (signed C (Nat.succ n)
      (eulerPrimitive C order f (Nat.succ n)))

def pointRemainder (n order : Nat) (f : Nat -> A) : A :=
  sub C (signed C n (f n)) (localBoundary C n order f)

def eulerBooleRemainder (start len order : Nat) (f : Nat -> A) : A :=
  rangeSum C start len (fun n => pointRemainder C n order f)

def eulerBooleRight (start len order : Nat) (f : Nat -> A) : A :=
  C.add (endpointCorrection C start len order f)
    (eulerBooleRemainder C start len order f)

private theorem add_sub_cancel_left_arg (x y : A) :
    C.eqv (C.add x (sub C y x)) y := by
  unfold sub
  exact C.trans (C.symm (C.add_assoc x y (C.neg x)))
    (C.trans
      (C.add_congr (C.add_comm x y) (C.refl (C.neg x)))
      (C.trans (C.add_assoc y x (C.neg x))
        (C.trans (C.add_congr (C.refl y) (C.add_neg x))
          (C.add_zero y))))

private theorem add_rebracket_tail (a b c : A) :
    C.eqv (C.add a (C.add b c)) (C.add b (C.add a c)) := by
  exact C.trans (C.symm (C.add_assoc a b c))
    (C.trans (C.add_congr (C.add_comm a b) (C.refl c))
      (C.add_assoc b a c))

private theorem sub_self_zero (x : A) :
    C.eqv (sub C x x) C.zero := by
  unfold sub
  exact C.add_neg x

private theorem sub_add_sub_cancel (x y z : A) :
    C.eqv (C.add (sub C x y) (sub C y z)) (sub C x z) := by
  unfold sub
  exact C.trans (C.add_assoc x (C.neg y) (C.add y (C.neg z)))
    (C.trans
      (C.add_congr (C.refl x)
        (C.symm (C.add_assoc (C.neg y) y (C.neg z))))
      (C.add_congr (C.refl x)
        (C.trans
          (C.add_congr (C.neg_add y) (C.refl (C.neg z)))
          (C.zero_add (C.neg z)))))

private theorem add_pair_reorder (a b c d : A) :
    C.eqv (C.add (C.add a b) (C.add c d))
      (C.add (C.add a c) (C.add b d)) := by
  exact C.trans (C.add_assoc a b (C.add c d))
    (C.trans
      (C.add_congr (C.refl a) (C.symm (C.add_assoc b c d)))
      (C.trans
        (C.add_congr (C.refl a)
          (C.add_congr (C.add_comm b c) (C.refl d)))
        (C.trans
          (C.add_congr (C.refl a) (C.add_assoc c b d))
          (C.symm (C.add_assoc a c (C.add b d))))))

private theorem localBoundary_endpoint (start len order : Nat) (f : Nat -> A) :
    C.eqv
      (C.add (localBoundary C start order f)
        (endpointCorrection C (Nat.succ start) len order f))
      (endpointCorrection C start (Nat.succ len) order f) := by
  unfold localBoundary endpointCorrection
  change
    C.eqv
      (C.add
        (sub C
          (signed C start (eulerPrimitive C order f start))
          (signed C (Nat.succ start)
            (eulerPrimitive C order f (Nat.succ start))))
        (sub C
          (signed C (Nat.succ start)
            (eulerPrimitive C order f (Nat.succ start)))
          (signed C (rangeEnd (Nat.succ start) len)
            (eulerPrimitive C order f (rangeEnd (Nat.succ start) len)))))
      (sub C
        (signed C start (eulerPrimitive C order f start))
        (signed C (rangeEnd (Nat.succ start) len)
          (eulerPrimitive C order f (rangeEnd (Nat.succ start) len))))
  exact sub_add_sub_cancel C
    (signed C start (eulerPrimitive C order f start))
    (signed C (Nat.succ start)
      (eulerPrimitive C order f (Nat.succ start)))
    (signed C (rangeEnd (Nat.succ start) len)
      (eulerPrimitive C order f (rangeEnd (Nat.succ start) len)))

private theorem pointRemainder_split (n order : Nat) (f : Nat -> A) :
    C.eqv
      (C.add (localBoundary C n order f)
        (pointRemainder C n order f))
      (signed C n (f n)) := by
  unfold pointRemainder
  exact add_sub_cancel_left_arg C (localBoundary C n order f) (signed C n (f n))

theorem endpointCorrection_step (start len order : Nat) (f : Nat -> A) :
    C.eqv
      (endpointCorrection C start len order f)
      (sub C
        (signed C start (eulerPrimitive C order f start))
        (signed C (rangeEnd start len)
          (eulerPrimitive C order f (rangeEnd start len)))) :=
  C.refl (endpointCorrection C start len order f)

theorem eulerBooleRemainder_step (start len order : Nat) (f : Nat -> A) :
    C.eqv
      (eulerBooleRemainder C start (Nat.succ len) order f)
      (C.add (pointRemainder C start order f)
        (eulerBooleRemainder C (Nat.succ start) len order f)) :=
  C.refl (eulerBooleRemainder C start (Nat.succ len) order f)

theorem finiteEulerBoole_identity
    (start len order : Nat) (f : Nat -> A) :
    C.eqv (alternatingRangeSum C start len f)
      (eulerBooleRight C start len order f) := by
  induction len generalizing start with
  | zero =>
      unfold alternatingRangeSum rangeSum eulerBooleRight eulerBooleRemainder
      unfold endpointCorrection rangeEnd
      exact C.symm
        (C.trans
          (C.add_zero
            (sub C
              (signed C start (eulerPrimitive C order f start))
              (signed C start (eulerPrimitive C order f start))))
          (sub_self_zero C
            (signed C start (eulerPrimitive C order f start))))
  | succ len ih =>
      have tail :=
        ih (Nat.succ start)
      have tailStep :
          C.eqv
            (C.add (signed C start (f start))
              (alternatingRangeSum C (Nat.succ start) len f))
            (C.add (signed C start (f start))
              (eulerBooleRight C (Nat.succ start) len order f)) :=
        C.add_congr (C.refl (signed C start (f start))) tail
      have splitStep :
          C.eqv
            (C.add (signed C start (f start))
              (eulerBooleRight C (Nat.succ start) len order f))
            (C.add
              (C.add (localBoundary C start order f)
                (pointRemainder C start order f))
              (eulerBooleRight C (Nat.succ start) len order f)) :=
        C.add_congr (C.symm (pointRemainder_split C start order f))
          (C.refl (eulerBooleRight C (Nat.succ start) len order f))
      have expanded :
          C.eqv
            (C.add
              (C.add (localBoundary C start order f)
                (pointRemainder C start order f))
              (eulerBooleRight C (Nat.succ start) len order f))
            (C.add
              (C.add (localBoundary C start order f)
                (pointRemainder C start order f))
              (C.add
                (endpointCorrection C (Nat.succ start) len order f)
                (eulerBooleRemainder C (Nat.succ start) len order f))) :=
        C.add_congr
          (C.refl
            (C.add (localBoundary C start order f)
              (pointRemainder C start order f)))
          (C.refl (eulerBooleRight C (Nat.succ start) len order f))
      have reordered :
          C.eqv
            (C.add
              (C.add (localBoundary C start order f)
                (pointRemainder C start order f))
              (C.add
                (endpointCorrection C (Nat.succ start) len order f)
                (eulerBooleRemainder C (Nat.succ start) len order f)))
            (C.add
              (C.add (localBoundary C start order f)
                (endpointCorrection C (Nat.succ start) len order f))
              (C.add
                (pointRemainder C start order f)
                (eulerBooleRemainder C (Nat.succ start) len order f))) :=
        add_pair_reorder C
          (localBoundary C start order f)
          (pointRemainder C start order f)
          (endpointCorrection C (Nat.succ start) len order f)
          (eulerBooleRemainder C (Nat.succ start) len order f)
      have endpointStep :
          C.eqv
            (C.add
              (C.add (localBoundary C start order f)
                (endpointCorrection C (Nat.succ start) len order f))
              (C.add
                (pointRemainder C start order f)
                (eulerBooleRemainder C (Nat.succ start) len order f)))
            (C.add
              (endpointCorrection C start (Nat.succ len) order f)
              (C.add
                (pointRemainder C start order f)
                (eulerBooleRemainder C (Nat.succ start) len order f))) :=
        C.add_congr
          (localBoundary_endpoint C start len order f)
          (C.refl
            (C.add
              (pointRemainder C start order f)
              (eulerBooleRemainder C (Nat.succ start) len order f)))
      exact C.trans tailStep
        (C.trans splitStep
          (C.trans expanded
            (C.trans reordered endpointStep)))

end AdditiveCarrier

def boolAdd : Bool -> Bool -> Bool
  | false, y => y
  | true, false => true
  | true, true => false

def boolCarrier : AdditiveCarrier Bool where
  zero := false
  add := boolAdd
  neg := fun x => x
  scale := fun _q x => x
  eqv := Eq
  refl := fun x => rfl
  symm := fun h => h.symm
  trans := fun h g => h.trans g
  add_congr := by
    intro x x' y y' hx hy
    cases hx
    cases hy
    rfl
  neg_congr := by
    intro x y h
    cases h
    rfl
  scale_congr := by
    intro q x y h
    cases h
    rfl
  add_assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  add_comm := by
    intro x y
    cases x <;> cases y <;> rfl
  add_zero := by
    intro x
    cases x <;> rfl
  zero_add := by
    intro x
    cases x <;> rfl
  add_neg := by
    intro x
    cases x <;> rfl
  neg_add := by
    intro x
    cases x <;> rfl

def sampleSeq : Nat -> Bool
  | 0 => false
  | Nat.succ 0 => true
  | _ => false

theorem sample_forwardDiff_zero :
    @AdditiveCarrier.eqv Bool boolCarrier
      (@AdditiveCarrier.forwardDiff Bool boolCarrier sampleSeq 0) true := by
  rfl

theorem eulerBoole_sample_readback :
    @AdditiveCarrier.eqv Bool boolCarrier
      (@AdditiveCarrier.alternatingRangeSum Bool boolCarrier 0 3 sampleSeq)
      (@AdditiveCarrier.eulerBooleRight Bool boolCarrier 0 3 2 sampleSeq) :=
  @AdditiveCarrier.finiteEulerBoole_identity Bool boolCarrier 0 3 2 sampleSeq

theorem eulerBoole_sample_left_value :
    @AdditiveCarrier.alternatingRangeSum Bool boolCarrier 0 3 sampleSeq = true := by
  rfl

theorem eulerBoole_sample_right_value :
    @AdditiveCarrier.eulerBooleRight Bool boolCarrier 0 3 2 sampleSeq = true := by
  rfl

end BEDC.Derived.EulerBooleSummation
