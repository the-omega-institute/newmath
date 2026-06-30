import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.EulerTransformUp.TasteGate
import BEDC.Derived.FiniteDifferenceUp.TasteGate

namespace BEDC.Derived.BinomialTransformUp

open BEDC.Algebra.Rel

variable {A : Type u} {r : A -> A -> Prop}

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def tailSeq (a : Nat -> A) : Nat -> A :=
  fun k => a (Nat.succ k)

def dropSeq (a : Nat -> A) (offset : Nat) : Nat -> A :=
  fun k => a (offset + k)

def binomialTransformAt (R : RelCommRing A r) (a : Nat -> A) : Nat -> A
  | 0 => a 0
  | Nat.succ n =>
      R.add (binomialTransformAt R a n)
        (binomialTransformAt R (tailSeq a) n)

def forwardDifferenceAt (R : RelCommRing A r) (b : Nat -> A) (i : Nat) : A :=
  R.sub (b (Nat.succ i)) (b i)

def iteratedForwardDifferenceAt (R : RelCommRing A r)
    (b : Nat -> A) : Nat -> Nat -> A
  | 0, i => b i
  | Nat.succ n, i =>
      R.sub (iteratedForwardDifferenceAt R b n (Nat.succ i))
        (iteratedForwardDifferenceAt R b n i)

def inverseBinomialTransformAt (R : RelCommRing A r)
    (b : Nat -> A) (n : Nat) : A :=
  iteratedForwardDifferenceAt R b n 0

def differenceColumn (R : RelCommRing A r)
    (b : Nat -> A) (i : Nat) : Nat -> A :=
  fun k => iteratedForwardDifferenceAt R b k i

def BinomialForwardRelated (R : RelCommRing A r)
    (a b : Nat -> A) : Prop :=
  forall n : Nat, r (b n) (binomialTransformAt R a n)

def BinomialInverseRelated (R : RelCommRing A r)
    (a b : Nat -> A) : Prop :=
  forall n : Nat, r (a n) (inverseBinomialTransformAt R b n)

def scaleNat (R : RelCommRing A r) : Nat -> A -> A
  | 0, _x => R.zero
  | Nat.succ n, x => R.add (scaleNat R n x) x

def binomialCoeffTerm (R : RelCommRing A r)
    (a : Nat -> A) (n k : Nat) : A :=
  scaleNat R (C n k) (a k)

def binomialCoeffPrefixSum (R : RelCommRing A r)
    (a : Nat -> A) (n : Nat) : Nat -> A
  | 0 => binomialCoeffTerm R a n 0
  | Nat.succ k =>
      R.add (binomialCoeffPrefixSum R a n k)
        (binomialCoeffTerm R a n (Nat.succ k))

def binomialCoeffSumAt (R : RelCommRing A r)
    (a : Nat -> A) (n : Nat) : A :=
  binomialCoeffPrefixSum R a n n

private theorem sub_congr (R : RelCommRing A r)
    {x x' y y' : A} :
    r x x' -> r y y' -> r (R.sub x y) (R.sub x' y') := by
  intro hx hy
  exact R.trans (R.sub_eq_add_neg x y)
    (R.trans (R.add_congr hx (R.neg_congr hy))
      (R.symm (R.sub_eq_add_neg x' y')))

private theorem sub_add_left (R : RelCommRing A r) (x y : A) :
    r (R.sub (R.add x y) x) y := by
  exact R.trans (R.sub_eq_add_neg (R.add x y) x)
    (R.trans
      (R.add_congr (R.add_comm x y) (R.refl (R.neg x)))
      (R.trans (R.add_assoc y x (R.neg x))
        (R.trans
          (R.add_congr (R.refl y) (R.add_neg x))
          (R.add_zero y))))

private theorem add_sub_cancel_left_arg (R : RelCommRing A r) (x y : A) :
    r (R.add x (R.sub y x)) y := by
  exact R.trans (R.add_congr (R.refl x) (R.sub_eq_add_neg y x))
    (R.trans (R.symm (R.add_assoc x y (R.neg x)))
      (R.trans
        (R.add_congr (R.add_comm x y) (R.refl (R.neg x)))
        (R.trans (R.add_assoc y x (R.neg x))
          (R.trans
            (R.add_congr (R.refl y) (R.add_neg x))
            (R.add_zero y)))))

private theorem add_four_swap (R : RelCommRing A r)
    (a b c d : A) :
    r (R.add (R.add a b) (R.add c d))
      (R.add (R.add a c) (R.add b d)) := by
  exact R.trans (R.add_assoc a b (R.add c d))
    (R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc b c d)))
      (R.trans
        (R.add_congr (R.refl a)
          (R.add_congr (R.add_comm b c) (R.refl d)))
        (R.trans
          (R.add_congr (R.refl a) (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (R.add b d))))))

theorem scaleNat_zero (R : RelCommRing A r) (x : A) :
    r (scaleNat R 0 x) R.zero :=
  R.refl R.zero

theorem scaleNat_one (R : RelCommRing A r) (x : A) :
    r (scaleNat R 1 x) x :=
  R.zero_add x

theorem scaleNat_congr (R : RelCommRing A r)
    {x y : A} :
    r x y -> forall n : Nat, r (scaleNat R n x) (scaleNat R n y)
  | _same, 0 =>
      R.refl R.zero
  | same, Nat.succ n =>
      R.add_congr (scaleNat_congr R same n) same

theorem scaleNat_add_coeff (R : RelCommRing A r)
    (m n : Nat) (x : A) :
    r (scaleNat R (m + n) x)
      (R.add (scaleNat R m x) (scaleNat R n x)) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      exact R.symm (R.add_zero (scaleNat R m x))
  | succ n ih =>
      rw [Nat.add_succ]
      change
        r (R.add (scaleNat R (m + n) x) x)
          (R.add (scaleNat R m x)
            (R.add (scaleNat R n x) x))
      exact R.trans
        (R.add_congr ih (R.refl x))
        (R.add_assoc (scaleNat R m x) (scaleNat R n x) x)

private theorem binomialCoeffTerm_pascal (R : RelCommRing A r)
    (a : Nat -> A) (n k : Nat) :
    r (binomialCoeffTerm R a (Nat.succ n) (Nat.succ k))
      (R.add (binomialCoeffTerm R (tailSeq a) n k)
        (binomialCoeffTerm R a n (Nat.succ k))) := by
  unfold binomialCoeffTerm
  unfold tailSeq
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n k]
  exact scaleNat_add_coeff R (C n k) (C n (Nat.succ k)) (a (Nat.succ k))

private theorem binomialCoeffTerm_zero_right_same
    (R : RelCommRing A r) (a : Nat -> A) (n : Nat) :
    r (binomialCoeffTerm R a (Nat.succ n) 0)
      (binomialCoeffTerm R a n 0) := by
  unfold binomialCoeffTerm
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right (Nat.succ n)]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  exact R.refl (scaleNat R 1 (a 0))

theorem binomialCoeffPrefix_above_self
    (R : RelCommRing A r) (a : Nat -> A) (n : Nat) :
    r (binomialCoeffPrefixSum R a n (Nat.succ n))
      (binomialCoeffPrefixSum R a n n) := by
  change
    r
      (R.add (binomialCoeffPrefixSum R a n n)
        (binomialCoeffTerm R a n (Nat.succ n)))
      (binomialCoeffPrefixSum R a n n)
  unfold binomialCoeffTerm
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_above n 0]
  exact R.add_zero (binomialCoeffPrefixSum R a n n)

theorem binomialCoeffPrefix_pascal (R : RelCommRing A r)
    (a : Nat -> A) (n : Nat) :
    forall k : Nat,
      r (binomialCoeffPrefixSum R a (Nat.succ n) (Nat.succ k))
        (R.add (binomialCoeffPrefixSum R a n (Nat.succ k))
          (binomialCoeffPrefixSum R (tailSeq a) n k))
  | 0 => by
      have first :
          r (binomialCoeffTerm R a (Nat.succ n) 0)
            (binomialCoeffTerm R a n 0) :=
        binomialCoeffTerm_zero_right_same R a n
      have second :
          r (binomialCoeffTerm R a (Nat.succ n) 1)
            (R.add (binomialCoeffTerm R (tailSeq a) n 0)
              (binomialCoeffTerm R a n 1)) := by
        have raw := binomialCoeffTerm_pascal R a n 0
        change
          r (binomialCoeffTerm R a (Nat.succ n) 1)
            (R.add (binomialCoeffTerm R (tailSeq a) n 0)
              (binomialCoeffTerm R a n 1)) at raw
        exact raw
      have expanded :
          r
            (R.add
              (binomialCoeffTerm R a (Nat.succ n) 0)
              (binomialCoeffTerm R a (Nat.succ n) 1))
            (R.add (binomialCoeffTerm R a n 0)
              (R.add (binomialCoeffTerm R (tailSeq a) n 0)
                (binomialCoeffTerm R a n 1))) := by
        exact R.add_congr first second
      have rebracket :
          r
            (R.add (binomialCoeffTerm R a n 0)
              (R.add (binomialCoeffTerm R (tailSeq a) n 0)
                (binomialCoeffTerm R a n 1)))
            (R.add
              (R.add (binomialCoeffTerm R a n 0)
                (binomialCoeffTerm R a n 1))
              (binomialCoeffTerm R (tailSeq a) n 0)) := by
        exact R.trans
          (R.add_congr (R.refl (binomialCoeffTerm R a n 0))
            (R.add_comm (binomialCoeffTerm R (tailSeq a) n 0)
              (binomialCoeffTerm R a n 1)))
          (R.symm
            (R.add_assoc (binomialCoeffTerm R a n 0)
              (binomialCoeffTerm R a n 1)
              (binomialCoeffTerm R (tailSeq a) n 0)))
      exact R.trans expanded rebracket
  | Nat.succ k => by
      have prefixStep :=
        binomialCoeffPrefix_pascal R a n k
      have termStep :
          r
            (binomialCoeffTerm R a (Nat.succ n) (Nat.succ (Nat.succ k)))
            (R.add (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))
              (binomialCoeffTerm R a n (Nat.succ (Nat.succ k)))) :=
        binomialCoeffTerm_pascal R a n (Nat.succ k)
      have termAligned :
          r
            (binomialCoeffTerm R a (Nat.succ n) (Nat.succ (Nat.succ k)))
            (R.add (binomialCoeffTerm R a n (Nat.succ (Nat.succ k)))
              (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))) :=
        R.trans termStep
          (R.add_comm
            (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))
            (binomialCoeffTerm R a n (Nat.succ (Nat.succ k))))
      have combined :
          r
            (R.add
              (binomialCoeffPrefixSum R a (Nat.succ n) (Nat.succ k))
              (binomialCoeffTerm R a (Nat.succ n) (Nat.succ (Nat.succ k))))
            (R.add
              (R.add (binomialCoeffPrefixSum R a n (Nat.succ k))
                (binomialCoeffPrefixSum R (tailSeq a) n k))
              (R.add (binomialCoeffTerm R a n (Nat.succ (Nat.succ k)))
                (binomialCoeffTerm R (tailSeq a) n (Nat.succ k)))) :=
        R.add_congr prefixStep termAligned
      have rearranged :
          r
            (R.add
              (R.add (binomialCoeffPrefixSum R a n (Nat.succ k))
                (binomialCoeffPrefixSum R (tailSeq a) n k))
              (R.add (binomialCoeffTerm R a n (Nat.succ (Nat.succ k)))
                (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))))
            (R.add
              (R.add (binomialCoeffPrefixSum R a n (Nat.succ k))
                (binomialCoeffTerm R a n (Nat.succ (Nat.succ k))))
              (R.add (binomialCoeffPrefixSum R (tailSeq a) n k)
                (binomialCoeffTerm R (tailSeq a) n (Nat.succ k)))) :=
        add_four_swap R
          (binomialCoeffPrefixSum R a n (Nat.succ k))
          (binomialCoeffPrefixSum R (tailSeq a) n k)
          (binomialCoeffTerm R a n (Nat.succ (Nat.succ k)))
          (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))
      change
        r
          (R.add
            (binomialCoeffPrefixSum R a (Nat.succ n) (Nat.succ k))
            (binomialCoeffTerm R a (Nat.succ n) (Nat.succ (Nat.succ k))))
          (R.add
            (R.add (binomialCoeffPrefixSum R a n (Nat.succ k))
              (binomialCoeffTerm R a n (Nat.succ (Nat.succ k))))
            (R.add (binomialCoeffPrefixSum R (tailSeq a) n k)
              (binomialCoeffTerm R (tailSeq a) n (Nat.succ k))))
      exact R.trans combined rearranged

theorem binomialTransformAt_binomialCoeffSum
    (R : RelCommRing A r) (a : Nat -> A) :
    forall n : Nat,
      r (binomialTransformAt R a n)
        (binomialCoeffSumAt R a n)
  | 0 => by
      unfold binomialCoeffSumAt binomialCoeffPrefixSum binomialCoeffTerm
      unfold C
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right 0]
      exact R.symm (scaleNat_one R (a 0))
  | Nat.succ n => by
      have head :=
        binomialTransformAt_binomialCoeffSum R a n
      have tail :=
        binomialTransformAt_binomialCoeffSum R (tailSeq a) n
      have toSums :
          r
            (binomialTransformAt R a (Nat.succ n))
            (R.add (binomialCoeffSumAt R a n)
              (binomialCoeffSumAt R (tailSeq a) n)) := by
        change
          r
            (R.add (binomialTransformAt R a n)
              (binomialTransformAt R (tailSeq a) n))
            (R.add (binomialCoeffSumAt R a n)
              (binomialCoeffSumAt R (tailSeq a) n))
        exact R.add_congr head tail
      have extendHead :
          r
            (R.add (binomialCoeffSumAt R a n)
              (binomialCoeffSumAt R (tailSeq a) n))
            (R.add
              (binomialCoeffPrefixSum R a n (Nat.succ n))
              (binomialCoeffSumAt R (tailSeq a) n)) := by
        unfold binomialCoeffSumAt
        exact R.add_congr
          (R.symm (binomialCoeffPrefix_above_self R a n))
          (R.refl (binomialCoeffPrefixSum R (tailSeq a) n n))
      have pascal :=
        binomialCoeffPrefix_pascal R a n n
      unfold binomialCoeffSumAt at pascal
      exact R.trans toSums
        (R.trans extendHead (R.symm pascal))

theorem binomialTransformAt_congr (R : RelCommRing A r)
    {a b : Nat -> A} :
    (forall k : Nat, r (a k) (b k)) ->
      forall n : Nat,
        r (binomialTransformAt R a n) (binomialTransformAt R b n)
  | same, 0 =>
      same 0
  | same, Nat.succ n =>
      R.add_congr
        (binomialTransformAt_congr R same n)
        (binomialTransformAt_congr R (fun k => same (Nat.succ k)) n)

theorem binomialTransform_zero (R : RelCommRing A r)
    (a : Nat -> A) :
    r (binomialTransformAt R a 0) (a 0) :=
  R.refl (a 0)

theorem binomialTransform_succ (R : RelCommRing A r)
    (a : Nat -> A) (n : Nat) :
    r (binomialTransformAt R a (Nat.succ n))
      (R.add (binomialTransformAt R a n)
        (binomialTransformAt R (tailSeq a) n)) :=
  R.refl (binomialTransformAt R a (Nat.succ n))

theorem binomialTransform_forwardDifference (R : RelCommRing A r)
    (a : Nat -> A) (i : Nat) :
    r
      (forwardDifferenceAt R
        (fun n => binomialTransformAt R a n) i)
      (binomialTransformAt R (tailSeq a) i) := by
  unfold forwardDifferenceAt
  change
    r
      (R.sub
        (R.add (binomialTransformAt R a i)
          (binomialTransformAt R (tailSeq a) i))
        (binomialTransformAt R a i))
      (binomialTransformAt R (tailSeq a) i)
  exact sub_add_left R
    (binomialTransformAt R a i)
    (binomialTransformAt R (tailSeq a) i)

theorem iteratedForwardDifference_congr (R : RelCommRing A r)
    {b c : Nat -> A} :
    (forall i : Nat, r (b i) (c i)) ->
      forall n i : Nat,
        r (iteratedForwardDifferenceAt R b n i)
          (iteratedForwardDifferenceAt R c n i)
  | same, 0, i =>
      same i
  | same, Nat.succ n, i =>
      sub_congr R
        (iteratedForwardDifference_congr R same n (Nat.succ i))
        (iteratedForwardDifference_congr R same n i)

theorem inverseBinomialTransformAt_congr (R : RelCommRing A r)
    {b c : Nat -> A} :
    (forall i : Nat, r (b i) (c i)) ->
      forall n : Nat,
        r (inverseBinomialTransformAt R b n)
          (inverseBinomialTransformAt R c n) := by
  intro same n
  unfold inverseBinomialTransformAt
  exact iteratedForwardDifference_congr R same n 0

theorem iteratedForwardDifference_forwardDifference
    (R : RelCommRing A r) (b : Nat -> A) :
    forall n i : Nat,
      r
        (iteratedForwardDifferenceAt R
          (forwardDifferenceAt R b) n i)
        (iteratedForwardDifferenceAt R b (Nat.succ n) i)
  | 0, i =>
      R.refl (forwardDifferenceAt R b i)
  | Nat.succ n, i =>
      sub_congr R
        (iteratedForwardDifference_forwardDifference R b n (Nat.succ i))
        (iteratedForwardDifference_forwardDifference R b n i)

private theorem tail_dropSeq_same (R : RelCommRing A r)
    (a : Nat -> A) (offset : Nat) :
    forall k : Nat,
      r (tailSeq (dropSeq a offset) k)
        (dropSeq a (Nat.succ offset) k) := by
  intro k
  unfold tailSeq dropSeq
  have index :
      offset + Nat.succ k = Nat.succ offset + k := by
    rw [Nat.add_succ, Nat.succ_add]
  rw [index]
  exact R.refl (a (Nat.succ offset + k))

private theorem dropSeq_zero_same (R : RelCommRing A r)
    (a : Nat -> A) :
    forall k : Nat, r (a k) (dropSeq a 0 k) := by
  intro k
  unfold dropSeq
  rw [Nat.zero_add]
  exact R.refl (a k)

theorem iteratedForwardDifference_binomialTransform_drop
    (R : RelCommRing A r) (a : Nat -> A) :
    forall n i : Nat,
      r
        (iteratedForwardDifferenceAt R
          (fun j => binomialTransformAt R a j) n i)
        (binomialTransformAt R (dropSeq a n) i)
  | 0, i =>
      binomialTransformAt_congr R (dropSeq_zero_same R a) i
  | Nat.succ n, i => by
      have stepToDifference :
          r
            (iteratedForwardDifferenceAt R
              (fun j => binomialTransformAt R a j) (Nat.succ n) i)
            (forwardDifferenceAt R
              (fun j => binomialTransformAt R (dropSeq a n) j) i) := by
        change
          r
            (R.sub
              (iteratedForwardDifferenceAt R
                (fun j => binomialTransformAt R a j) n (Nat.succ i))
              (iteratedForwardDifferenceAt R
                (fun j => binomialTransformAt R a j) n i))
            (R.sub
              (binomialTransformAt R (dropSeq a n) (Nat.succ i))
              (binomialTransformAt R (dropSeq a n) i))
        exact sub_congr R
          (iteratedForwardDifference_binomialTransform_drop R a n (Nat.succ i))
          (iteratedForwardDifference_binomialTransform_drop R a n i)
      have differenceToTail :
          r
            (forwardDifferenceAt R
              (fun j => binomialTransformAt R (dropSeq a n) j) i)
            (binomialTransformAt R (tailSeq (dropSeq a n)) i) :=
        binomialTransform_forwardDifference R (dropSeq a n) i
      have tailToDrop :
          r (binomialTransformAt R (tailSeq (dropSeq a n)) i)
            (binomialTransformAt R (dropSeq a (Nat.succ n)) i) :=
        binomialTransformAt_congr R (tail_dropSeq_same R a n) i
      exact R.trans stepToDifference
        (R.trans differenceToTail tailToDrop)

theorem inverseBinomialTransform_binomialTransform
    (R : RelCommRing A r) (a : Nat -> A) (n : Nat) :
    r
      (inverseBinomialTransformAt R
        (fun j => binomialTransformAt R a j) n)
      (a n) := by
  unfold inverseBinomialTransformAt
  have recovered :=
    iteratedForwardDifference_binomialTransform_drop R a n 0
  have readZero :
      r (binomialTransformAt R (dropSeq a n) 0) (a n) := by
    change r (dropSeq a n 0) (a n)
    unfold dropSeq
    rw [Nat.add_zero]
    exact R.refl (a n)
  exact R.trans recovered readZero

theorem binomialTransform_differenceColumn
    (R : RelCommRing A r) (b : Nat -> A) :
    forall n i : Nat,
      r (binomialTransformAt R (differenceColumn R b i) n)
        (b (i + n))
  | 0, i => by
      change r (b i) (b (i + 0))
      rw [Nat.add_zero]
      exact R.refl (b i)
  | Nat.succ n, i => by
      have head :
          r (binomialTransformAt R (differenceColumn R b i) n)
            (b (i + n)) :=
        binomialTransform_differenceColumn R b n i
      have tailColumn :
          forall k : Nat,
            r (tailSeq (differenceColumn R b i) k)
              (differenceColumn R (forwardDifferenceAt R b) i k) := by
        intro k
        unfold tailSeq differenceColumn
        exact R.symm
          (iteratedForwardDifference_forwardDifference R b k i)
      have tailTransform :
          r
            (binomialTransformAt R
              (tailSeq (differenceColumn R b i)) n)
            (binomialTransformAt R
              (differenceColumn R (forwardDifferenceAt R b) i) n) :=
        binomialTransformAt_congr R tailColumn n
      have tailRead :
          r
            (binomialTransformAt R
              (differenceColumn R (forwardDifferenceAt R b) i) n)
            (forwardDifferenceAt R b (i + n)) :=
        binomialTransform_differenceColumn R
          (forwardDifferenceAt R b) n i
      have tail :
          r
            (binomialTransformAt R
              (tailSeq (differenceColumn R b i)) n)
            (forwardDifferenceAt R b (i + n)) :=
        R.trans tailTransform tailRead
      have combined :
          r
            (binomialTransformAt R
              (differenceColumn R b i) (Nat.succ n))
            (R.add (b (i + n))
              (forwardDifferenceAt R b (i + n))) := by
        change
          r
            (R.add
              (binomialTransformAt R (differenceColumn R b i) n)
              (binomialTransformAt R
                (tailSeq (differenceColumn R b i)) n))
            (R.add (b (i + n))
              (forwardDifferenceAt R b (i + n)))
        exact R.add_congr head tail
      have cancel :
          r
            (R.add (b (i + n))
              (forwardDifferenceAt R b (i + n)))
            (b (Nat.succ (i + n))) := by
        unfold forwardDifferenceAt
        exact add_sub_cancel_left_arg R
          (b (i + n)) (b (Nat.succ (i + n)))
      have index :
          r (b (Nat.succ (i + n))) (b (i + Nat.succ n)) := by
        rw [Nat.add_succ]
        exact R.refl (b (Nat.succ (i + n)))
      exact R.trans combined (R.trans cancel index)

theorem binomialTransform_inverseBinomialTransform
    (R : RelCommRing A r) (b : Nat -> A) (n : Nat) :
    r
      (binomialTransformAt R
        (fun k => inverseBinomialTransformAt R b k) n)
      (b n) := by
  unfold inverseBinomialTransformAt
  change
    r
      (binomialTransformAt R
        (differenceColumn R b 0) n)
      (b n)
  have h := binomialTransform_differenceColumn R b n 0
  change
    r
      (binomialTransformAt R
        (differenceColumn R b 0) n)
      (b (0 + n)) at h
  rw [Nat.zero_add] at h
  exact h

theorem binomial_inversion_forward_to_inverse
    (R : RelCommRing A r) {a b : Nat -> A} :
    BinomialForwardRelated R a b ->
      BinomialInverseRelated R a b := by
  intro forward n
  have sameInverse :
      r (inverseBinomialTransformAt R b n)
        (inverseBinomialTransformAt R
          (fun j => binomialTransformAt R a j) n) :=
    inverseBinomialTransformAt_congr R forward n
  have recovered :
      r
        (inverseBinomialTransformAt R
          (fun j => binomialTransformAt R a j) n)
        (a n) :=
    inverseBinomialTransform_binomialTransform R a n
  exact R.symm (R.trans sameInverse recovered)

theorem binomial_inversion_inverse_to_forward
    (R : RelCommRing A r) {a b : Nat -> A} :
    BinomialInverseRelated R a b ->
      BinomialForwardRelated R a b := by
  intro inverse n
  have sameForward :
      r (binomialTransformAt R a n)
        (binomialTransformAt R
          (fun k => inverseBinomialTransformAt R b k) n) :=
    binomialTransformAt_congr R inverse n
  have recovered :
      r
        (binomialTransformAt R
          (fun k => inverseBinomialTransformAt R b k) n)
        (b n) :=
    binomialTransform_inverseBinomialTransform R b n
  exact R.symm (R.trans sameForward recovered)

theorem binomial_inversion_bidirectional
    (R : RelCommRing A r) (a b : Nat -> A) :
    BinomialForwardRelated R a b <->
      BinomialInverseRelated R a b := by
  constructor
  · exact binomial_inversion_forward_to_inverse R
  · exact binomial_inversion_inverse_to_forward R

theorem binomial_transform_self_inverse_pair
    (R : RelCommRing A r) :
    (forall (a : Nat -> A) (n : Nat),
      r
        (inverseBinomialTransformAt R
          (fun j => binomialTransformAt R a j) n)
        (a n)) ∧
      (forall (b : Nat -> A) (n : Nat),
        r
          (binomialTransformAt R
            (fun k => inverseBinomialTransformAt R b k) n)
          (b n)) := by
  constructor
  · intro a n
    exact inverseBinomialTransform_binomialTransform R a n
  · intro b n
    exact binomialTransform_inverseBinomialTransform R b n

theorem binomialTransform_finiteDifference_link
    (R : RelCommRing A r) (a : Nat -> A) (i : Nat) :
    r
      (forwardDifferenceAt R
        (fun n => binomialTransformAt R a n) i)
      (binomialTransformAt R (tailSeq a) i) :=
  binomialTransform_forwardDifference R a i

def eulerFiniteDifferenceColumn (R : RelCommRing A r)
    (b : Nat -> A) (n : Nat) : A :=
  inverseBinomialTransformAt R b n

theorem eulerFiniteDifferenceColumn_binomialInverse
    (R : RelCommRing A r) (b : Nat -> A) (n : Nat) :
    r (eulerFiniteDifferenceColumn R b n)
      (iteratedForwardDifferenceAt R b n 0) :=
  R.refl (eulerFiniteDifferenceColumn R b n)

theorem eulerTransform_tasteGate_available :
    Nonempty
      (BEDC.Meta.TasteGate.ChapterTasteGate
        BEDC.Derived.EulerTransformUp.EulerTransformUp) :=
  ⟨BEDC.Derived.EulerTransformUp.eulerTransformChapterTasteGate⟩

theorem finiteDifference_tasteGate_available :
    Nonempty
      (BEDC.Meta.TasteGate.ChapterTasteGate
        BEDC.Derived.FiniteDifferenceUp.FiniteDifferenceUp) :=
  ⟨BEDC.Derived.FiniteDifferenceUp.finiteDifferenceChapterTasteGate⟩

def zeroSeq (R : RelCommRing A r) : Nat -> A :=
  fun _ => R.zero

def oneSeq (R : RelCommRing A r) : Nat -> A :=
  fun _ => R.one

def unitSpikeSeq (R : RelCommRing A r) : Nat -> A
  | 0 => R.one
  | Nat.succ _ => R.zero

theorem binomialTransform_zeroSeq (R : RelCommRing A r) :
    forall n : Nat,
      r (binomialTransformAt R (zeroSeq R) n) R.zero
  | 0 =>
      R.refl R.zero
  | Nat.succ n => by
      have head := binomialTransform_zeroSeq R n
      have tailSame :
          forall k : Nat,
            r (tailSeq (zeroSeq R) k) (zeroSeq R k) := by
        intro k
        exact R.refl R.zero
      have tailMove :
          r (binomialTransformAt R (tailSeq (zeroSeq R)) n)
            (binomialTransformAt R (zeroSeq R) n) :=
        binomialTransformAt_congr R tailSame n
      have tail :
          r (binomialTransformAt R (tailSeq (zeroSeq R)) n)
            R.zero :=
        R.trans tailMove (binomialTransform_zeroSeq R n)
      exact R.trans
        (R.add_congr head tail)
        (R.zero_add R.zero)

private theorem tail_unitSpike_zeroSeq
    (R : RelCommRing A r) :
    forall k : Nat,
      r (tailSeq (unitSpikeSeq R) k) (zeroSeq R k) := by
  intro k
  exact R.refl R.zero

theorem binomialTransform_unitSpikeSeq
    (R : RelCommRing A r) :
    forall n : Nat,
      r (binomialTransformAt R (unitSpikeSeq R) n) R.one
  | 0 =>
      R.refl R.one
  | Nat.succ n => by
      have head := binomialTransform_unitSpikeSeq R n
      have tailMove :
          r (binomialTransformAt R (tailSeq (unitSpikeSeq R)) n)
            (binomialTransformAt R (zeroSeq R) n) :=
        binomialTransformAt_congr R (tail_unitSpike_zeroSeq R) n
      have tail :
          r (binomialTransformAt R (tailSeq (unitSpikeSeq R)) n)
            R.zero :=
        R.trans tailMove (binomialTransform_zeroSeq R n)
      exact R.trans
        (R.add_congr head tail)
        (R.add_zero R.one)

theorem binomialInversion_unitSpike_constant_example
    (R : RelCommRing A r) :
    BinomialForwardRelated R (unitSpikeSeq R) (oneSeq R) ∧
      BinomialInverseRelated R (unitSpikeSeq R) (oneSeq R) := by
  have forward :
      BinomialForwardRelated R (unitSpikeSeq R) (oneSeq R) := by
    intro n
    exact R.symm (binomialTransform_unitSpikeSeq R n)
  exact
    ⟨forward,
      binomial_inversion_forward_to_inverse R forward⟩

theorem BinomialTransformUp_constructive_export
    (R : RelCommRing A r) :
    (forall a b : Nat -> A,
      BinomialForwardRelated R a b <->
        BinomialInverseRelated R a b) ∧
      (forall a n,
        r (binomialTransformAt R a n)
          (binomialCoeffSumAt R a n)) ∧
      (forall a n,
        r
          (inverseBinomialTransformAt R
            (fun j => binomialTransformAt R a j) n)
          (a n)) ∧
      (forall b n,
        r
          (binomialTransformAt R
            (fun k => inverseBinomialTransformAt R b k) n)
          (b n)) ∧
      BinomialForwardRelated R (unitSpikeSeq R) (oneSeq R) := by
  constructor
  · intro a b
    exact binomial_inversion_bidirectional R a b
  · constructor
    · intro a n
      exact binomialTransformAt_binomialCoeffSum R a n
    · constructor
      · intro a n
        exact inverseBinomialTransform_binomialTransform R a n
      · constructor
        · intro b n
          exact binomialTransform_inverseBinomialTransform R b n
        · exact (binomialInversion_unitSpike_constant_example R).left

end BEDC.Derived.BinomialTransformUp
