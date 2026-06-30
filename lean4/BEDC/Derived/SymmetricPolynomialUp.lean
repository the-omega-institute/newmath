import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.SymmetricPolynomialUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold

universe u

variable {A : Type u} {rel : A -> A -> Prop}

def ringPow (R : RelCommRing A rel) (x : A) : Nat -> A
  | 0 => R.one
  | Nat.succ n => R.mul x (ringPow R x n)

def natScale (R : RelCommRing A rel) : Nat -> A -> A
  | 0, _x => R.zero
  | Nat.succ 0, x => x
  | Nat.succ (Nat.succ n), x => R.add x (natScale R (Nat.succ n) x)

def signedByParity (R : RelCommRing A rel) : Nat -> A -> A
  | 0, x => x
  | Nat.succ 0, x => R.neg x
  | Nat.succ (Nat.succ n), x => signedByParity R n x

def elementarySymmetricFuel (R : RelCommRing A rel) : Nat -> Nat -> List A -> A
  | _fuel, 0, _roots => R.one
  | 0, Nat.succ _k, _roots => R.zero
  | Nat.succ _fuel, Nat.succ _k, [] => R.zero
  | Nat.succ fuel, Nat.succ k, root :: roots =>
      R.add (elementarySymmetricFuel R fuel (Nat.succ k) roots)
        (R.mul root (elementarySymmetricFuel R fuel k roots))

def elementarySymmetric (R : RelCommRing A rel) (k : Nat) (roots : List A) : A :=
  elementarySymmetricFuel R roots.length k roots

def powerSum (R : RelCommRing A rel) (roots : List A) (k : Nat) : A :=
  listSum R (List.map (fun root => ringPow R root k) roots)

def newtonMiddle (R : RelCommRing A rel) (roots : List A) (k : Nat) :
    Nat -> Nat -> A
  | 0, _i => R.zero
  | Nat.succ fuel, i =>
      R.add
        (signedByParity R i
          (R.mul (elementarySymmetric R i roots)
            (powerSum R roots (k - i))))
        (newtonMiddle R roots k fuel (Nat.succ i))

def newtonStep (R : RelCommRing A rel) (roots : List A) : Nat -> A
  | 0 => R.zero
  | Nat.succ k =>
      R.add (powerSum R roots (Nat.succ k))
        (R.add (newtonMiddle R roots (Nat.succ k) k 1)
          (signedByParity R (Nat.succ k)
            (natScale R (Nat.succ k)
              (elementarySymmetric R (Nat.succ k) roots))))

def linearFactorCoeffs (R : RelCommRing A rel) (root : A) : List A :=
  [R.neg root, R.one]

def vietaLinearCoeffs (R : RelCommRing A rel) (root : A) : List A :=
  [signedByParity R 1 (elementarySymmetric R 1 [root]),
    signedByParity R 0 (elementarySymmetric R 0 [root])]

theorem ringPow_one (R : RelCommRing A rel) (x : A) :
    rel (ringPow R x 1) x :=
  R.mul_one x

theorem natScale_one (R : RelCommRing A rel) (x : A) :
    rel (natScale R 1 x) x :=
  R.refl x

theorem elementarySymmetric_zero (R : RelCommRing A rel) (roots : List A) :
    rel (elementarySymmetric R 0 roots) R.one := by
  cases roots with
  | nil =>
      exact R.refl R.one
  | cons _ _ =>
      exact R.refl R.one

theorem elementarySymmetric_succ_nil (R : RelCommRing A rel) (k : Nat) :
    rel (elementarySymmetric R (Nat.succ k) []) R.zero :=
  R.refl R.zero

theorem elementarySymmetric_succ_cons (R : RelCommRing A rel)
    (k : Nat) (root : A) (roots : List A) :
    rel (elementarySymmetric R (Nat.succ k) (root :: roots))
      (R.add (elementarySymmetric R (Nat.succ k) roots)
        (R.mul root (elementarySymmetric R k roots))) :=
  R.refl
    (R.add (elementarySymmetric R (Nat.succ k) roots)
      (R.mul root (elementarySymmetric R k roots)))

theorem powerSum_nil (R : RelCommRing A rel) (k : Nat) :
    rel (powerSum R [] k) R.zero :=
  R.refl R.zero

theorem powerSum_cons (R : RelCommRing A rel)
    (root : A) (roots : List A) (k : Nat) :
    rel (powerSum R (root :: roots) k)
      (R.add (ringPow R root k) (powerSum R roots k)) :=
  R.refl (R.add (ringPow R root k) (powerSum R roots k))

theorem powerSum_one_eq_elementarySymmetric_one (R : RelCommRing A rel) :
    ∀ roots : List A, rel (powerSum R roots 1) (elementarySymmetric R 1 roots)
  | [] =>
      R.refl R.zero
  | root :: roots => by
      have tail := powerSum_one_eq_elementarySymmetric_one R roots
      have headToRoot : rel (ringPow R root 1) root :=
        ringPow_one R root
      have step :
          rel (R.add (ringPow R root 1) (powerSum R roots 1))
            (R.add root (elementarySymmetric R 1 roots)) :=
        R.add_congr headToRoot tail
      have commute :
          rel (R.add root (elementarySymmetric R 1 roots))
            (R.add (elementarySymmetric R 1 roots) root) :=
        R.add_comm root (elementarySymmetric R 1 roots)
      have oneRight :
          rel (R.add (elementarySymmetric R 1 roots) root)
            (R.add (elementarySymmetric R 1 roots) (R.mul root R.one)) :=
        R.add_congr (R.refl (elementarySymmetric R 1 roots))
          (R.symm (R.mul_one root))
      have oneToEZero : rel R.one (elementarySymmetric R 0 roots) :=
        R.symm (elementarySymmetric_zero R roots)
      have eZeroRight :
          rel (R.add (elementarySymmetric R 1 roots) (R.mul root R.one))
            (R.add (elementarySymmetric R 1 roots)
              (R.mul root (elementarySymmetric R 0 roots))) :=
        R.add_congr (R.refl (elementarySymmetric R 1 roots))
          (R.mul_congr (R.refl root) oneToEZero)
      exact R.trans step (R.trans commute (R.trans oneRight eZeroRight))

def newtonDegreeOneLeft (R : RelCommRing A rel) (roots : List A) : A :=
  R.add (powerSum R roots 1) (R.neg (elementarySymmetric R 1 roots))

theorem newtonDegreeOneLeft_zero (R : RelCommRing A rel) (roots : List A) :
    rel (newtonDegreeOneLeft R roots) R.zero := by
  have same := powerSum_one_eq_elementarySymmetric_one R roots
  exact R.trans
    (R.add_congr same (R.refl (R.neg (elementarySymmetric R 1 roots))))
    (R.add_neg (elementarySymmetric R 1 roots))

theorem newtonStep_degreeOne_zero (R : RelCommRing A rel) (roots : List A) :
    rel (newtonStep R roots 1) R.zero := by
  have foldZero :
      rel (newtonStep R roots 1) (newtonDegreeOneLeft R roots) :=
    R.add_congr (R.refl (powerSum R roots 1))
      (R.zero_add (R.neg (elementarySymmetric R 1 roots)))
  exact R.trans foldZero (newtonDegreeOneLeft_zero R roots)

theorem elementarySymmetric_one_singleton (R : RelCommRing A rel) (root : A) :
    rel (elementarySymmetric R 1 [root]) root :=
  R.trans (R.zero_add (R.mul root R.one)) (R.mul_one root)

theorem powerSum_one_singleton (R : RelCommRing A rel) (root : A) :
    rel (powerSum R [root] 1) root :=
  R.trans (R.add_zero (ringPow R root 1)) (ringPow_one R root)

theorem vieta_linear_factor (R : RelCommRing A rel) (root : A) :
    ListPairwiseRel rel (linearFactorCoeffs R root) (vietaLinearCoeffs R root) := by
  have eOneToRoot : rel (elementarySymmetric R 1 [root]) root :=
    elementarySymmetric_one_singleton R root
  have first :
      rel (R.neg root) (R.neg (elementarySymmetric R 1 [root])) :=
    R.neg_congr (R.symm eOneToRoot)
  have second : rel R.one (elementarySymmetric R 0 [root]) :=
    R.refl R.one
  exact ListPairwiseRel.cons first (ListPairwiseRel.cons second ListPairwiseRel.nil)

end BEDC.Derived.SymmetricPolynomialUp
