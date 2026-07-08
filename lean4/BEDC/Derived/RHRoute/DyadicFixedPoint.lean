import BEDC.Derived.BernoulliUp

namespace BEDC.Derived.RHRoute.DyadicFixedPoint

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

structure DyadicFixedPoint (p : Nat) where
  num : Int
  deriving DecidableEq, Repr

structure DyRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving Repr

def DyRat.eqv (x y : DyRat) : Prop :=
  x.num * Int.ofNat y.den = y.num * Int.ofNat x.den

def DyRat.le (x y : DyRat) : Prop :=
  x.num * Int.ofNat y.den ≤ y.num * Int.ofNat x.den

def DyRat.lt (x y : DyRat) : Prop :=
  x.num * Int.ofNat y.den < y.num * Int.ofNat x.den

instance : LE DyRat where
  le := DyRat.le

instance : LT DyRat where
  lt := DyRat.lt

def DyRat.add (x y : DyRat) : DyRat :=
  { num := x.num * Int.ofNat y.den + y.num * Int.ofNat x.den
    den := x.den * y.den
    den_pos := Nat.mul_pos x.den_pos y.den_pos }

def DyRat.neg (x : DyRat) : DyRat :=
  { num := -x.num
    den := x.den
    den_pos := x.den_pos }

def DyRat.sub (x y : DyRat) : DyRat :=
  { num := x.num * Int.ofNat y.den - y.num * Int.ofNat x.den
    den := x.den * y.den
    den_pos := Nat.mul_pos x.den_pos y.den_pos }

def DyRat.mul (x y : DyRat) : DyRat :=
  { num := x.num * y.num
    den := x.den * y.den
    den_pos := Nat.mul_pos x.den_pos y.den_pos }

instance : Add DyRat where
  add := DyRat.add

instance : Neg DyRat where
  neg := DyRat.neg

instance : Sub DyRat where
  sub := DyRat.sub

instance : Mul DyRat where
  mul := DyRat.mul

theorem DyRat.eqv_refl (x : DyRat) : DyRat.eqv x x := by
  unfold DyRat.eqv
  rfl

theorem DyRat.eqv_symm {x y : DyRat} :
    DyRat.eqv x y -> DyRat.eqv y x := by
  intro h
  exact h.symm

def scaleUnit (p : Nat) : Int :=
  Int.ofNat ((2 : Nat) ^ p)

def scaleNat (p : Nat) : Nat :=
  (2 : Nat) ^ p

theorem scaleNat_pos (p : Nat) : 0 < scaleNat p :=
  Nat.pow_pos (Nat.succ_pos 1)

def halfDown : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | Nat.succ (Nat.succ n) => halfDown n + 1

def halfRem : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => halfRem n

private theorem doubleSuccRepack (a : Nat) :
    (a + a) + (1 + 1) = (a + 1) + (a + 1) := by
  calc
    (a + a) + (1 + 1) = ((a + a) + 1) + 1 := (Nat.add_assoc (a + a) 1 1).symm
    _ = (a + (a + 1)) + 1 := by rw [Nat.add_assoc a a 1]
    _ = (a + (1 + a)) + 1 := by rw [Nat.add_comm a 1]
    _ = ((a + 1) + a) + 1 := by rw [Nat.add_assoc a 1 a]
    _ = (a + 1) + (a + 1) := Nat.add_assoc (a + 1) a 1

private theorem halfRepack (a r : Nat) :
    ((a + a + r) + 1) + 1 = (a + 1) + (a + 1) + r := by
  calc
    ((a + a + r) + 1) + 1 = (a + a + r) + (1 + 1) := Nat.add_assoc (a + a + r) 1 1
    _ = (a + a) + (r + (1 + 1)) := by rw [Nat.add_assoc (a + a) r (1 + 1)]
    _ = (a + a) + ((1 + 1) + r) := by rw [Nat.add_comm r (1 + 1)]
    _ = ((a + a) + (1 + 1)) + r := (Nat.add_assoc (a + a) (1 + 1) r).symm
    _ = (a + 1) + (a + 1) + r := by rw [doubleSuccRepack a]

theorem halfDown_decomp : ∀ n : Nat, n = halfDown n + halfDown n + halfRem n
  | 0 => rfl
  | 1 => rfl
  | Nat.succ (Nat.succ n) => by
      have ih := halfDown_decomp n
      calc
        Nat.succ (Nat.succ n) = (n + 1) + 1 := rfl
        _ = ((halfDown n + halfDown n + halfRem n) + 1) + 1 :=
            congrArg (fun t => (t + 1) + 1) ih
        _ = (halfDown n + 1) + (halfDown n + 1) + halfRem n :=
            halfRepack (halfDown n) (halfRem n)

theorem halfRem_lt_two : ∀ n : Nat, halfRem n < 2
  | 0 => by decide
  | 1 => by decide
  | Nat.succ (Nat.succ n) => halfRem_lt_two n

def divPow2Down : Nat -> Nat -> Nat
  | 0, n => n
  | Nat.succ p, n => divPow2Down p (halfDown n)

-- Lean core `Nat.mul_assoc` carries a transitive `propext` dependency, which the
-- BEDC zero-axiom invariant forbids; this local induction on `c` reproves it from
-- `Nat.mul_succ`/`Nat.mul_add` (both propext-free) so the floor bounds stay pure.
theorem natMulAssoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Nat.mul_succ, Nat.mul_succ, ih, Nat.mul_add]

theorem divPow2Down_mul_le : ∀ (p n : Nat),
    divPow2Down p n * (2 : Nat) ^ p ≤ n
  | 0, n => by
      change n * 1 ≤ n
      rw [Nat.mul_one]
      exact Nat.le_refl n
  | Nat.succ p, n => by
      have ihLo := divPow2Down_mul_le p (halfDown n)
      have hdLeN : 2 * halfDown n ≤ n := by
        calc
          2 * halfDown n = halfDown n + halfDown n :=
            Nat.two_mul (halfDown n)
          _ ≤ halfDown n + halfDown n + halfRem n :=
            Nat.le_add_right _ _
          _ = n := (halfDown_decomp n).symm
      have doubled :
          2 * (divPow2Down p (halfDown n) * (2 : Nat) ^ p) ≤ n :=
        Nat.le_trans (Nat.mul_le_mul_left 2 ihLo) hdLeN
      calc
        divPow2Down (Nat.succ p) n * (2 : Nat) ^ Nat.succ p
            = 2 * (divPow2Down p (halfDown n) * (2 : Nat) ^ p) := by
              dsimp [divPow2Down]
              calc
                divPow2Down p (halfDown n) * (2 : Nat) ^ Nat.succ p
                    = divPow2Down p (halfDown n) * ((2 : Nat) ^ p * 2) := by
                        rw [Nat.pow_succ]
                _ = divPow2Down p (halfDown n) * (2 : Nat) ^ p * 2 :=
                    (natMulAssoc (divPow2Down p (halfDown n))
                      ((2 : Nat) ^ p) 2).symm
                _ = 2 * (divPow2Down p (halfDown n) * (2 : Nat) ^ p) := by
                    rw [Nat.mul_comm (divPow2Down p (halfDown n) * (2 : Nat) ^ p) 2]
        _ ≤ n := doubled

theorem divPow2Down_lt_succ : ∀ (p n : Nat),
    n < (divPow2Down p n + 1) * (2 : Nat) ^ p
  | 0, n => by
      change n < (n + 1) * 1
      rw [Nat.mul_one]
      exact Nat.lt_succ_self n
  | Nat.succ p, n => by
      have ihHi := divPow2Down_lt_succ p (halfDown n)
      have ihLe : halfDown n + 1 ≤
          (divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ p :=
        Nat.succ_le_of_lt ihHi
      have doubledLe :
          2 * (halfDown n + 1) ≤
            2 * ((divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ p) :=
        Nat.mul_le_mul_left 2 ihLe
      have remLe : halfRem n + 1 ≤ 2 :=
        Nat.succ_le_of_lt (halfRem_lt_two n)
      have succNLe : n + 1 ≤ 2 * halfDown n + 2 := by
        calc
          n + 1 = (halfDown n + halfDown n + halfRem n) + 1 :=
            congrArg (fun t => t + 1) (halfDown_decomp n)
          _ = 2 * halfDown n + (halfRem n + 1) := by
            rw [Nat.add_assoc, ← Nat.two_mul]
          _ ≤ 2 * halfDown n + 2 :=
            Nat.add_le_add_left remLe (2 * halfDown n)
      have targetLe : 2 * halfDown n + 2 ≤
          (divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ Nat.succ p := by
        calc
          2 * halfDown n + 2 = 2 * (halfDown n + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ ≤ 2 * ((divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ p) :=
            doubledLe
          _ = (divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ Nat.succ p := by
            calc
              2 * ((divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ p)
                  = ((divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ p) * 2 :=
                    Nat.mul_comm 2 _
              _ = (divPow2Down p (halfDown n) + 1) * ((2 : Nat) ^ p * 2) :=
                  natMulAssoc (divPow2Down p (halfDown n) + 1) ((2 : Nat) ^ p) 2
              _ = (divPow2Down p (halfDown n) + 1) * (2 : Nat) ^ Nat.succ p := by
                  rw [Nat.pow_succ]
      have succGoal : n + 1 ≤
          (divPow2Down (Nat.succ p) n + 1) * (2 : Nat) ^ Nat.succ p := by
        dsimp [divPow2Down]
        exact Nat.le_trans succNLe targetLe
      exact Nat.lt_of_succ_le succGoal

def dyOfInt (p : Nat) (k : Int) : Int :=
  k * scaleUnit p

def dyAdd (x y : Int) : Int :=
  x + y

def dyNeg (x : Int) : Int :=
  -x

def dyMulDown (p : Nat) (x y : Int) : Int :=
  (x * y) / scaleUnit p

def dyLe (x y : Int) : Prop :=
  x ≤ y

def dyVal (p : Nat) (x : Int) : DyRat :=
  { num := x
    den := scaleNat p
    den_pos := scaleNat_pos p }

def dyValRatNum (p : Nat) (x : Int) : Rat :=
  BEDC.Derived.BernoulliUp.rawRatToRat
    { num := x, denMinusOne := (2 : Nat) ^ p - 1 }

structure DyAddCertificate (p : Nat) (x y : Int) where
  val_eqv :
    DyRat.eqv (dyVal p (dyAdd x y))
      (DyRat.add (dyVal p x) (dyVal p y))

structure DyLeCertificate (p : Nat) (x y : Int) where
  val_le : DyRat.le (dyVal p x) (dyVal p y)

theorem dyValRatNum_den_readback (p : Nat) (x : Int) :
    (dyValRatNum p x).den = BEDC.Derived.IntUp.natToUnary ((2 : Nat) ^ p) := by
  unfold dyValRatNum BEDC.Derived.BernoulliUp.rawRatToRat
    BEDC.Derived.BernoulliUp.RawRat.den
  change
    BEDC.Derived.IntUp.natToUnary (((2 : Nat) ^ p - 1).succ) =
      BEDC.Derived.IntUp.natToUnary ((2 : Nat) ^ p)
  rw [← Nat.pred_eq_sub_one]
  rw [Nat.succ_pred_eq_of_pos
    (Nat.pow_pos (Nat.succ_pos 1) : 0 < (2 : Nat) ^ p)]

theorem dyNeg_val (p : Nat) (x : Int) :
    dyVal p (dyNeg x) = -dyVal p x := by
  unfold dyVal dyNeg
  rfl

theorem dyAdd_val (p : Nat) (x y : Int)
    (cert : DyAddCertificate p x y) :
    DyRat.eqv (dyVal p (dyAdd x y))
      (DyRat.add (dyVal p x) (dyVal p y)) :=
  cert.val_eqv

theorem dyLe_sound (p : Nat) (x y : Int)
    (_h : dyLe x y) (cert : DyLeCertificate p x y) :
    DyRat.le (dyVal p x) (dyVal p y) :=
  cert.val_le

-- BOUNDARY (signed-Int dyMulDown floor bound, deferred). The general bound
--   dyMulDown p x y * scaleUnit p ≤ x*y < (dyMulDown p x y + 1) * scaleUnit p
-- (for 0 ≤ x*y) is exactly the Nat floor pair `divPow2Down_mul_le` /
-- `divPow2Down_lt_succ` transported across `Int.ofNat`. It is NOT recorded as a
-- theorem here because every Lean-core `Int.ediv` bound lemma (`Int.ediv_mul_le`,
-- `Int.lt_ediv_add_one_mul_self`, `Int.sub_lt_iff`, …) carries a transitive
-- `propext` dependency, which the BEDC zero-axiom / propext-free invariant forbids.
-- The upgrade path is a propext-free Int-division layer (reprove the Int floor
-- bounds from `Int.ediv`'s definition via the clean Nat `divPow2Down` bounds and
-- `Int.ofNat` monotonicity); the Nat carrier bounds below are the certified core.

def dyadicPrecision : Nat :=
  20

def dyadicScale : Int :=
  scaleUnit dyadicPrecision

def dyThreeQuarter : Int :=
  3 * scaleUnit dyadicPrecision / 4

def dyOneHalf : Int :=
  scaleUnit dyadicPrecision / 2

def dyThreeEighth : Int :=
  3 * scaleUnit dyadicPrecision / 8

theorem dyadicScale_readback :
    dyadicScale = 1048576 := by
  decide

theorem dyThreeQuarter_readback :
    dyThreeQuarter = 786432 := by
  decide

theorem dyOneHalf_readback :
    dyOneHalf = 524288 := by
  decide

theorem dyMulDown_three_quarter_one_half_readback :
    dyMulDown dyadicPrecision dyThreeQuarter dyOneHalf = dyThreeEighth := by
  decide

end BEDC.Derived.RHRoute.DyadicFixedPoint
