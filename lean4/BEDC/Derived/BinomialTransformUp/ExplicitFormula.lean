import BEDC.Derived.BinomialTransformUp

namespace BEDC.Derived.BinomialTransformUp

open BEDC.Algebra.Rel

variable {A : Type u} {r : A -> A -> Prop}

def ExplicitBinomialForwardRelated (R : RelCommRing A r)
    (a b : Nat -> A) : Prop :=
  forall n : Nat, r (b n) (binomialCoeffSumAt R a n)

def flipSign : Bool -> Bool
  | true => false
  | false => true

def rowInitialSign : Nat -> Bool
  | 0 => true
  | Nat.succ n => flipSign (rowInitialSign n)

def alternatingBinomialSign : Nat -> Nat -> Bool
  | n, 0 => rowInitialSign n
  | n, Nat.succ k => flipSign (alternatingBinomialSign n k)

def signedScaleNat (R : RelCommRing A r) : Bool -> Nat -> A -> A
  | true, coeff, x => scaleNat R coeff x
  | false, coeff, x => R.neg (scaleNat R coeff x)

def alternatingBinomialCoeffTerm (R : RelCommRing A r)
    (b : Nat -> A) (n i k : Nat) : A :=
  signedScaleNat R (alternatingBinomialSign n k) (C n k) (b (i + k))

def alternatingBinomialCoeffPrefixSum (R : RelCommRing A r)
    (b : Nat -> A) (n i : Nat) : Nat -> A
  | 0 => alternatingBinomialCoeffTerm R b n i 0
  | Nat.succ k =>
      R.add (alternatingBinomialCoeffPrefixSum R b n i k)
        (alternatingBinomialCoeffTerm R b n i (Nat.succ k))

def alternatingBinomialCoeffSumAt (R : RelCommRing A r)
    (b : Nat -> A) (n i : Nat) : A :=
  alternatingBinomialCoeffPrefixSum R b n i n

def inverseBinomialCoeffSumAt (R : RelCommRing A r)
    (b : Nat -> A) (n : Nat) : A :=
  alternatingBinomialCoeffSumAt R b n 0

def ExplicitBinomialInverseRelated (R : RelCommRing A r)
    (a b : Nat -> A) : Prop :=
  forall n : Nat, r (a n) (inverseBinomialCoeffSumAt R b n)

private theorem flipSign_flipSign (s : Bool) :
    flipSign (flipSign s) = s := by
  cases s <;> rfl

private theorem alternatingBinomialSign_succ_left_succ
    (n k : Nat) :
    alternatingBinomialSign (Nat.succ n) (Nat.succ k) =
      alternatingBinomialSign n k := by
  induction k with
  | zero =>
      change flipSign (flipSign (rowInitialSign n)) = rowInitialSign n
      exact flipSign_flipSign (rowInitialSign n)
  | succ k ih =>
      unfold alternatingBinomialSign
      rw [ih]

private theorem succ_add_same (i k : Nat) :
    Nat.succ i + k = i + Nat.succ k := by
  rw [Nat.succ_add, Nat.add_succ]

private theorem sub_congr (R : RelCommRing A r)
    {x x' y y' : A} :
    r x x' -> r y y' -> r (R.sub x y) (R.sub x' y') := by
  intro hx hy
  exact R.trans (R.sub_eq_add_neg x y)
    (R.trans (R.add_congr hx (R.neg_congr hy))
      (R.symm (R.sub_eq_add_neg x' y')))

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

private theorem neg_add (R : RelCommRing A r) (x y : A) :
    r (R.neg (R.add x y)) (R.add (R.neg x) (R.neg y)) := by
  have inverse :
      r (R.add (R.add x y) (R.add (R.neg x) (R.neg y)))
        R.zero := by
    exact R.trans
      (R.add_assoc x y (R.add (R.neg x) (R.neg y)))
      (R.trans
        (R.add_congr (R.refl x)
          (R.trans (R.symm (R.add_assoc y (R.neg x) (R.neg y)))
            (R.trans
              (R.add_congr (R.add_comm y (R.neg x)) (R.refl (R.neg y)))
              (R.add_assoc (R.neg x) y (R.neg y)))))
        (R.trans
          (R.symm (R.add_assoc x (R.neg x) (R.add y (R.neg y))))
          (R.trans
            (R.add_congr (R.add_neg x) (R.add_neg y))
            (R.zero_add R.zero))))
  exact R.symm (R.eq_neg_of_add_eq_zero inverse)

private theorem signedScaleNat_congr (R : RelCommRing A r)
    {x y : A} (same : r x y) :
    forall (s : Bool) (coeff : Nat),
      r (signedScaleNat R s coeff x)
        (signedScaleNat R s coeff y)
  | true, coeff =>
      scaleNat_congr R same coeff
  | false, coeff =>
      R.neg_congr (scaleNat_congr R same coeff)

private theorem signedScaleNat_zero_coeff
    (R : RelCommRing A r) (s : Bool) (x : A) :
    r (signedScaleNat R s 0 x) R.zero := by
  cases s
  · exact R.trans (R.neg_congr (scaleNat_zero R x)) R.neg_zero
  · exact scaleNat_zero R x

private theorem signedScaleNat_add_coeff
    (R : RelCommRing A r) (s : Bool)
    (m n : Nat) (x : A) :
    r (signedScaleNat R s (m + n) x)
      (R.add (signedScaleNat R s m x)
        (signedScaleNat R s n x)) := by
  cases s
  · exact R.trans
      (R.neg_congr (scaleNat_add_coeff R m n x))
      (neg_add R (scaleNat R m x) (scaleNat R n x))
  · exact scaleNat_add_coeff R m n x

private theorem signedScaleNat_flip
    (R : RelCommRing A r) (s : Bool) (coeff : Nat) (x : A) :
    r (signedScaleNat R (flipSign s) coeff x)
      (R.neg (signedScaleNat R s coeff x)) := by
  cases s
  · exact R.symm (R.neg_neg (scaleNat R coeff x))
  · exact R.refl (R.neg (scaleNat R coeff x))

private theorem signedScaleNat_neg_flip
    (R : RelCommRing A r) (s : Bool) (coeff : Nat) (x : A) :
    r (R.neg (signedScaleNat R (flipSign s) coeff x))
      (signedScaleNat R s coeff x) := by
  cases s
  · exact R.refl (R.neg (scaleNat R coeff x))
  · exact R.neg_neg (scaleNat R coeff x)

private theorem alternatingCoeffTerm_head
    (R : RelCommRing A r) (b : Nat -> A) (n i : Nat) :
    r (alternatingBinomialCoeffTerm R b (Nat.succ n) i 0)
      (R.neg (alternatingBinomialCoeffTerm R b n i 0)) := by
  unfold alternatingBinomialCoeffTerm
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right (Nat.succ n)]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
  exact signedScaleNat_flip R (alternatingBinomialSign n 0) 1 (b (i + 0))

private theorem alternatingCoeffTerm_pascal
    (R : RelCommRing A r) (b : Nat -> A) (n i k : Nat) :
    r (alternatingBinomialCoeffTerm R b (Nat.succ n) i (Nat.succ k))
      (R.add (alternatingBinomialCoeffTerm R b n (Nat.succ i) k)
        (R.neg (alternatingBinomialCoeffTerm R b n i (Nat.succ k)))) := by
  unfold alternatingBinomialCoeffTerm
  rw [alternatingBinomialSign_succ_left_succ n k]
  rw [succ_add_same i k]
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n k]
  let s := alternatingBinomialSign n k
  let x := b (i + Nat.succ k)
  have split :
      r (signedScaleNat R s
          (BEDC.Derived.BinomialIdentitiesUp.C n k +
            BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x)
        (R.add
          (signedScaleNat R s (BEDC.Derived.BinomialIdentitiesUp.C n k) x)
          (signedScaleNat R s
            (BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x)) :=
    signedScaleNat_add_coeff R s
      (BEDC.Derived.BinomialIdentitiesUp.C n k)
      (BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x
  have rightMove :
      r
        (R.add
          (signedScaleNat R s (BEDC.Derived.BinomialIdentitiesUp.C n k) x)
          (R.neg
            (signedScaleNat R (flipSign s)
              (BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x)))
        (R.add
          (signedScaleNat R s (BEDC.Derived.BinomialIdentitiesUp.C n k) x)
          (signedScaleNat R s
            (BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x)) :=
    R.add_congr (R.refl _)
      (signedScaleNat_neg_flip R s
        (BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ k)) x)
  exact R.trans split (R.symm rightMove)

private theorem neg_add_left_to_sub
    (R : RelCommRing A r) (x y z : A) :
    r (R.add (R.neg y) (R.add x (R.neg z)))
      (R.sub x (R.add y z)) := by
  exact R.trans
    (R.trans
      (R.symm (R.add_assoc (R.neg y) x (R.neg z)))
      (R.trans
        (R.add_congr (R.add_comm (R.neg y) x) (R.refl (R.neg z)))
        (R.add_assoc x (R.neg y) (R.neg z))))
    (R.trans
      (R.add_congr (R.refl x) (R.symm (neg_add R y z)))
      (R.symm (R.sub_eq_add_neg x (R.add y z))))

private theorem sub_add_sub_to_sub_add
    (R : RelCommRing A r) (p q x y : A) :
    r (R.add (R.sub p q) (R.add x (R.neg y)))
      (R.sub (R.add p x) (R.add q y)) := by
  exact R.trans
    (R.add_congr (R.sub_eq_add_neg p q) (R.refl (R.add x (R.neg y))))
    (R.trans
      (add_four_swap R p (R.neg q) x (R.neg y))
      (R.trans
        (R.add_congr (R.refl (R.add p x)) (R.symm (neg_add R q y)))
        (R.symm (R.sub_eq_add_neg (R.add p x) (R.add q y)))))

private theorem alternatingCoeffPrefix_above_self
    (R : RelCommRing A r) (b : Nat -> A) (n i : Nat) :
    r (alternatingBinomialCoeffPrefixSum R b n i (Nat.succ n))
      (alternatingBinomialCoeffPrefixSum R b n i n) := by
  change
    r
      (R.add (alternatingBinomialCoeffPrefixSum R b n i n)
        (alternatingBinomialCoeffTerm R b n i (Nat.succ n)))
      (alternatingBinomialCoeffPrefixSum R b n i n)
  unfold alternatingBinomialCoeffTerm
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_above n 0]
  exact R.trans
    (R.add_congr (R.refl _) (signedScaleNat_zero_coeff R _ _))
    (R.add_zero (alternatingBinomialCoeffPrefixSum R b n i n))

private theorem alternatingCoeffPrefix_pascal
    (R : RelCommRing A r) (b : Nat -> A) (n i : Nat) :
    forall k : Nat,
      r (alternatingBinomialCoeffPrefixSum R b (Nat.succ n) i (Nat.succ k))
        (R.sub (alternatingBinomialCoeffPrefixSum R b n (Nat.succ i) k)
          (alternatingBinomialCoeffPrefixSum R b n i (Nat.succ k)))
  | 0 => by
      have head := alternatingCoeffTerm_head R b n i
      have step := alternatingCoeffTerm_pascal R b n i 0
      have combined :
          r
            (R.add (alternatingBinomialCoeffTerm R b (Nat.succ n) i 0)
              (alternatingBinomialCoeffTerm R b (Nat.succ n) i 1))
            (R.add (R.neg (alternatingBinomialCoeffTerm R b n i 0))
              (R.add (alternatingBinomialCoeffTerm R b n (Nat.succ i) 0)
                (R.neg (alternatingBinomialCoeffTerm R b n i 1)))) :=
        R.add_congr head step
      exact R.trans combined
        (neg_add_left_to_sub R
          (alternatingBinomialCoeffTerm R b n (Nat.succ i) 0)
          (alternatingBinomialCoeffTerm R b n i 0)
          (alternatingBinomialCoeffTerm R b n i 1))
  | Nat.succ k => by
      have prefixStep := alternatingCoeffPrefix_pascal R b n i k
      have termStep :=
        alternatingCoeffTerm_pascal R b n i (Nat.succ k)
      have combined :
          r
            (R.add
              (alternatingBinomialCoeffPrefixSum R b (Nat.succ n) i (Nat.succ k))
              (alternatingBinomialCoeffTerm R b (Nat.succ n) i
                (Nat.succ (Nat.succ k))))
            (R.add
              (R.sub (alternatingBinomialCoeffPrefixSum R b n (Nat.succ i) k)
                (alternatingBinomialCoeffPrefixSum R b n i (Nat.succ k)))
              (R.add
                (alternatingBinomialCoeffTerm R b n (Nat.succ i)
                  (Nat.succ k))
                (R.neg
                  (alternatingBinomialCoeffTerm R b n i
                    (Nat.succ (Nat.succ k)))))) :=
        R.add_congr prefixStep termStep
      exact R.trans combined
        (sub_add_sub_to_sub_add R
          (alternatingBinomialCoeffPrefixSum R b n (Nat.succ i) k)
          (alternatingBinomialCoeffPrefixSum R b n i (Nat.succ k))
          (alternatingBinomialCoeffTerm R b n (Nat.succ i) (Nat.succ k))
          (alternatingBinomialCoeffTerm R b n i (Nat.succ (Nat.succ k))))

theorem iteratedForwardDifference_alternatingBinomialCoeffSum
    (R : RelCommRing A r) (b : Nat -> A) :
    forall n i : Nat,
      r (iteratedForwardDifferenceAt R b n i)
        (alternatingBinomialCoeffSumAt R b n i)
  | 0, i => by
      unfold iteratedForwardDifferenceAt alternatingBinomialCoeffSumAt
      unfold alternatingBinomialCoeffPrefixSum alternatingBinomialCoeffTerm
      unfold C
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right 0]
      rw [Nat.add_zero]
      exact R.symm (scaleNat_one R (b i))
  | Nat.succ n, i => by
      have left :=
        iteratedForwardDifference_alternatingBinomialCoeffSum R b n (Nat.succ i)
      have right :=
        iteratedForwardDifference_alternatingBinomialCoeffSum R b n i
      have toSub :
          r
            (iteratedForwardDifferenceAt R b (Nat.succ n) i)
            (R.sub (alternatingBinomialCoeffSumAt R b n (Nat.succ i))
              (alternatingBinomialCoeffSumAt R b n i)) := by
        change
          r
            (R.sub (iteratedForwardDifferenceAt R b n (Nat.succ i))
              (iteratedForwardDifferenceAt R b n i))
            (R.sub (alternatingBinomialCoeffSumAt R b n (Nat.succ i))
              (alternatingBinomialCoeffSumAt R b n i))
        exact sub_congr R left right
      have pascal := alternatingCoeffPrefix_pascal R b n i n
      unfold alternatingBinomialCoeffSumAt at pascal
      have trimRight :
          r
            (R.sub (alternatingBinomialCoeffPrefixSum R b n (Nat.succ i) n)
              (alternatingBinomialCoeffPrefixSum R b n i n))
            (R.sub (alternatingBinomialCoeffPrefixSum R b n (Nat.succ i) n)
              (alternatingBinomialCoeffPrefixSum R b n i (Nat.succ n))) :=
        sub_congr R (R.refl _)
          (R.symm (alternatingCoeffPrefix_above_self R b n i))
      exact R.trans toSub
        (R.trans trimRight (R.symm pascal))

theorem inverseBinomialTransformAt_explicit_alternating_sum
    (R : RelCommRing A r) (b : Nat -> A) (n : Nat) :
    r (inverseBinomialTransformAt R b n)
      (inverseBinomialCoeffSumAt R b n) := by
  unfold inverseBinomialTransformAt inverseBinomialCoeffSumAt
  exact iteratedForwardDifference_alternatingBinomialCoeffSum R b n 0

theorem explicit_alternating_inverse_to_difference_inverse
    (R : RelCommRing A r) {a b : Nat -> A} :
    ExplicitBinomialInverseRelated R a b ->
      BinomialInverseRelated R a b := by
  intro inverse n
  exact R.trans (inverse n)
    (R.symm (inverseBinomialTransformAt_explicit_alternating_sum R b n))

theorem difference_inverse_to_explicit_alternating_inverse
    (R : RelCommRing A r) {a b : Nat -> A} :
    BinomialInverseRelated R a b ->
      ExplicitBinomialInverseRelated R a b := by
  intro inverse n
  exact R.trans (inverse n)
    (inverseBinomialTransformAt_explicit_alternating_sum R b n)

theorem explicit_forward_to_recursive_forward
    (R : RelCommRing A r) {a b : Nat -> A} :
    ExplicitBinomialForwardRelated R a b ->
      BinomialForwardRelated R a b := by
  intro forward n
  exact R.trans (forward n)
    (R.symm (binomialTransformAt_binomialCoeffSum R a n))

theorem recursive_forward_to_explicit_forward
    (R : RelCommRing A r) {a b : Nat -> A} :
    BinomialForwardRelated R a b ->
      ExplicitBinomialForwardRelated R a b := by
  intro forward n
  exact R.trans (forward n)
    (binomialTransformAt_binomialCoeffSum R a n)

theorem binomial_inversion_explicit_forward_to_inverse
    (R : RelCommRing A r) {a b : Nat -> A} :
    ExplicitBinomialForwardRelated R a b ->
      ExplicitBinomialInverseRelated R a b := by
  intro forward
  exact difference_inverse_to_explicit_alternating_inverse R
    (binomial_inversion_forward_to_inverse R
      (explicit_forward_to_recursive_forward R forward))

theorem binomial_inversion_inverse_to_explicit_forward
    (R : RelCommRing A r) {a b : Nat -> A} :
    ExplicitBinomialInverseRelated R a b ->
      ExplicitBinomialForwardRelated R a b := by
  intro inverse
  exact recursive_forward_to_explicit_forward R
    (binomial_inversion_inverse_to_forward R
      (explicit_alternating_inverse_to_difference_inverse R inverse))

theorem binomial_inversion_explicit_bidirectional
    (R : RelCommRing A r) (a b : Nat -> A) :
    ExplicitBinomialForwardRelated R a b <->
      ExplicitBinomialInverseRelated R a b := by
  constructor
  · exact binomial_inversion_explicit_forward_to_inverse R
  · exact binomial_inversion_inverse_to_explicit_forward R

theorem BinomialTransformUp_explicit_formula_export
    (R : RelCommRing A r) :
    (forall a b : Nat -> A,
      ExplicitBinomialForwardRelated R a b <->
        ExplicitBinomialInverseRelated R a b) ∧
      (forall a n,
        r (binomialTransformAt R a n)
          (binomialCoeffSumAt R a n)) ∧
      (forall b n,
        r (inverseBinomialTransformAt R b n)
          (inverseBinomialCoeffSumAt R b n)) := by
  constructor
  · intro a b
    exact binomial_inversion_explicit_bidirectional R a b
  · constructor
    · intro a n
      exact binomialTransformAt_binomialCoeffSum R a n
    · intro b n
      exact inverseBinomialTransformAt_explicit_alternating_sum R b n

end BEDC.Derived.BinomialTransformUp
