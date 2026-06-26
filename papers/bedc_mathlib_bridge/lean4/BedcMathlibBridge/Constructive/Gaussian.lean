import BEDC.Derived.GaussianUp
import Mathlib.Algebra.Ring.Equiv
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import BedcGate.Provenance
import BedcMathlibBridge.Constructive.Int

namespace BedcMathlibBridge.Constructive.Gaussian

open BEDC.Derived.GaussianUp
open BedcMathlibBridge.Constructive.Int

private def zLaws : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

private theorem zadd_right {a b c : BEDC.Derived.PrimeUp.IntegerUp} (h : Zeq a b) :
    Zeq (Zadd a c) (Zadd b c) :=
  zLaws.add_respects h (zLaws.eq_refl c)

private theorem zadd_left {a b c : BEDC.Derived.PrimeUp.IntegerUp} (h : Zeq a b) :
    Zeq (Zadd c a) (Zadd c b) :=
  zLaws.add_respects (zLaws.eq_refl c) h

private theorem z_eq_neg_of_add_eq_zero {a b : BEDC.Derived.PrimeUp.IntegerUp} :
    Zeq (Zadd a b) Zzero -> Zeq b (Zneg a) := by
  intro h
  exact zLaws.eq_trans (zLaws.eq_symm (zLaws.zero_add b))
    (zLaws.eq_trans
      (zadd_right (a := Zzero) (b := Zadd (Zneg a) a) (c := b)
        (zLaws.eq_symm (zLaws.neg_add a)))
      (zLaws.eq_trans (zLaws.add_assoc (Zneg a) a b)
        (zLaws.eq_trans (zadd_left (a := Zadd a b) (b := Zzero) (c := Zneg a) h)
          (zLaws.add_zero (Zneg a)))))

private theorem zMul_neg_right (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    Zeq (Zmul a (Zneg b)) (Zneg (Zmul a b)) := by
  have hzero : Zeq (Zadd (Zmul a b) (Zmul a (Zneg b))) Zzero := by
    exact zLaws.eq_trans
      (zLaws.eq_symm (zLaws.left_distrib a b (Zneg b)))
      (zLaws.eq_trans
        (zLaws.mul_respects (zLaws.eq_refl a) (zLaws.add_neg b))
        (zLaws.mul_zero a))
  exact z_eq_neg_of_add_eq_zero (a := Zmul a b) (b := Zmul a (Zneg b)) hzero

private theorem zMul_neg_left (a b : BEDC.Derived.PrimeUp.IntegerUp) :
    Zeq (Zmul (Zneg a) b) (Zneg (Zmul a b)) := by
  exact zLaws.eq_trans (zLaws.mul_comm (Zneg a) b)
    (zLaws.eq_trans (zMul_neg_right b a)
      (zLaws.neg_respects (zLaws.mul_comm b a)))

def zToInt (x : BEDC.Derived.PrimeUp.IntegerUp) : _root_.Int :=
  BedcMathlibBridge.Constructive.Int.toInt
    (BEDC.Derived.RationalUp.intToPair x)

def zOfInt (n : _root_.Int) : BEDC.Derived.PrimeUp.IntegerUp :=
  BEDC.Derived.RationalUp.pairToInt
    (BedcMathlibBridge.Constructive.Int.ofInt n)

theorem zRelIff {x y : BEDC.Derived.PrimeUp.IntegerUp} :
    BEDC.Derived.RationalUp.IntEq x y ↔ zToInt x = zToInt y := by
  unfold BEDC.Derived.RationalUp.IntEq zToInt
  exact BedcMathlibBridge.Constructive.Int.relIff
    (BEDC.Derived.RationalUp.intToPair_carrier x).left
    (BEDC.Derived.RationalUp.intToPair_carrier x).right
    (BEDC.Derived.RationalUp.intToPair_carrier y).left
    (BEDC.Derived.RationalUp.intToPair_carrier y).right

theorem zOfInt_toInt (n : _root_.Int) : zToInt (zOfInt n) = n := by
  unfold zToInt zOfInt
  have sourceCarrier :
      BEDC.Derived.IntUp.IntPairCarrier
        (BedcMathlibBridge.Constructive.Int.ofInt n).1
        (BedcMathlibBridge.Constructive.Int.ofInt n).2 :=
    (BedcMathlibBridge.Constructive.Int.CInt.ofInt n).property.left
  calc
    BedcMathlibBridge.Constructive.Int.toInt
        (BEDC.Derived.RationalUp.intToPair
          (BEDC.Derived.RationalUp.pairToInt
            (BedcMathlibBridge.Constructive.Int.ofInt n))) =
      BedcMathlibBridge.Constructive.Int.toInt
        (BedcMathlibBridge.Constructive.Int.ofInt n) :=
        (BedcMathlibBridge.Constructive.Int.relIff
          (BEDC.Derived.RationalUp.intToPair_carrier
            (BEDC.Derived.RationalUp.pairToInt
              (BedcMathlibBridge.Constructive.Int.ofInt n))).left
          (BEDC.Derived.RationalUp.intToPair_carrier
            (BEDC.Derived.RationalUp.pairToInt
              (BedcMathlibBridge.Constructive.Int.ofInt n))).right
          sourceCarrier.left
          sourceCarrier.right).mp
            (BEDC.Derived.RationalUp.intToPair_pairToInt_classifier
              (BedcMathlibBridge.Constructive.Int.ofInt n)
              sourceCarrier)
    _ = n := BedcMathlibBridge.Constructive.Int.rightInv n

theorem zOfInt_zToInt_rel (x : BEDC.Derived.PrimeUp.IntegerUp) :
    BEDC.Derived.RationalUp.IntEq (zOfInt (zToInt x)) x := by
  unfold BEDC.Derived.RationalUp.IntEq zToInt zOfInt
  have sourceCarrier :=
    (BedcMathlibBridge.Constructive.Int.CInt.ofInt
      (BedcMathlibBridge.Constructive.Int.toInt
        (BEDC.Derived.RationalUp.intToPair x))).property.left
  exact
    BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left
      (BEDC.Derived.RationalUp.intToPair_pairToInt_classifier
        (BedcMathlibBridge.Constructive.Int.ofInt
          (BedcMathlibBridge.Constructive.Int.toInt
            (BEDC.Derived.RationalUp.intToPair x)))
        sourceCarrier)
      (BedcMathlibBridge.Constructive.Int.leftInvRel
        (BEDC.Derived.RationalUp.intToPair_carrier x))

private theorem zToInt_pairToInt_eq {x : BEDC.FKernel.Hist.BHist × BEDC.FKernel.Hist.BHist}
    (hx : BEDC.Derived.IntUp.IntPairCarrier x.1 x.2) :
    zToInt (BEDC.Derived.RationalUp.pairToInt x) =
      BedcMathlibBridge.Constructive.Int.toInt x := by
  unfold zToInt
  exact (BedcMathlibBridge.Constructive.Int.relIff
    (BEDC.Derived.RationalUp.intToPair_carrier
      (BEDC.Derived.RationalUp.pairToInt x)).left
    (BEDC.Derived.RationalUp.intToPair_carrier
      (BEDC.Derived.RationalUp.pairToInt x)).right
    hx.left
    hx.right).mp
      (BEDC.Derived.RationalUp.intToPair_pairToInt_classifier x hx)

theorem zToInt_add (x y : BEDC.Derived.PrimeUp.IntegerUp) :
    zToInt (BEDC.Derived.RationalUp.IntAdd x y) = zToInt x + zToInt y := by
  unfold BEDC.Derived.RationalUp.IntAdd BEDC.Derived.RationalUp.intAdd
  have hx := BEDC.Derived.RationalUp.intToPair_carrier x
  have hy := BEDC.Derived.RationalUp.intToPair_carrier y
  have hxy :
      BEDC.Derived.IntUp.IntPairCarrier
        (BEDC.Derived.IntUp.pairAdd
          (BEDC.Derived.RationalUp.intToPair x)
          (BEDC.Derived.RationalUp.intToPair y)).1
        (BEDC.Derived.IntUp.pairAdd
          (BEDC.Derived.RationalUp.intToPair x)
          (BEDC.Derived.RationalUp.intToPair y)).2 :=
    BEDC.Derived.IntUp.pairAdd_carrier hx hy
  rw [zToInt_pairToInt_eq hxy]
  exact BedcMathlibBridge.Constructive.Int.pairAdd_toInt hx hy

theorem zToInt_neg (x : BEDC.Derived.PrimeUp.IntegerUp) :
    zToInt (BEDC.Derived.RationalUp.IntNeg x) = -zToInt x := by
  unfold BEDC.Derived.RationalUp.IntNeg BEDC.Derived.RationalUp.intNeg
  have hx := BEDC.Derived.RationalUp.intToPair_carrier x
  have hxNeg :
      BEDC.Derived.IntUp.IntPairCarrier
        (BEDC.Derived.IntUp.pairNeg (BEDC.Derived.RationalUp.intToPair x)).1
        (BEDC.Derived.IntUp.pairNeg (BEDC.Derived.RationalUp.intToPair x)).2 :=
    BEDC.Derived.IntUp.pairNeg_carrier hx
  rw [zToInt_pairToInt_eq hxNeg]
  exact BedcMathlibBridge.Constructive.Int.pairNeg_toInt
    (BEDC.Derived.RationalUp.intToPair x)

theorem zToInt_mul (x y : BEDC.Derived.PrimeUp.IntegerUp) :
    zToInt (BEDC.Derived.RationalUp.IntMul x y) = zToInt x * zToInt y := by
  unfold BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intMul
  have hx := BEDC.Derived.RationalUp.intToPair_carrier x
  have hy := BEDC.Derived.RationalUp.intToPair_carrier y
  have hxy :
      BEDC.Derived.IntUp.IntPairCarrier
        (BEDC.Derived.IntUp.pairMul
          (BEDC.Derived.RationalUp.intToPair x)
          (BEDC.Derived.RationalUp.intToPair y)).1
        (BEDC.Derived.IntUp.pairMul
          (BEDC.Derived.RationalUp.intToPair x)
          (BEDC.Derived.RationalUp.intToPair y)).2 :=
    BEDC.Derived.IntUp.pairMul_carrier hx hy
  rw [zToInt_pairToInt_eq hxy]
  exact BedcMathlibBridge.Constructive.Int.pairMul_toInt hx hy

theorem zToInt_zero : zToInt BEDC.Derived.RationalUp.intZero = 0 := by
  unfold zToInt BEDC.Derived.RationalUp.intZero BEDC.Derived.RationalUp.intOfNat
  exact BedcMathlibBridge.Constructive.Int.zero_toInt

theorem zToInt_one : zToInt BEDC.Derived.RationalUp.intOne = 1 := by
  unfold zToInt BEDC.Derived.RationalUp.intOne BEDC.Derived.RationalUp.intOfNat
  unfold BEDC.Derived.RationalUp.intToPair
  change BedcMathlibBridge.Constructive.Int.toInt
      (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty,
        BEDC.FKernel.Hist.BHist.Empty) = 1
  unfold BedcMathlibBridge.Constructive.Int.toInt
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨emptyLength, succLength, _noZero, _sameIff, _contAdd⟩
  rw [succLength BEDC.FKernel.Hist.BHist.Empty BEDC.FKernel.Unary.unary_empty]
  rw [emptyLength]
  rfl

theorem zToInt_neg_mul (x y : BEDC.Derived.PrimeUp.IntegerUp) :
    zToInt (Zneg (Zmul x y)) = (-1 : _root_.Int) * zToInt x * zToInt y := by
  have negOneMulX : Zeq (Zmul (Zneg Zone) x) (Zneg x) := by
    exact zLaws.eq_trans (zMul_neg_left Zone x)
      (zLaws.neg_respects (zLaws.one_mul x))
  have negMulXY :
      Zeq (Zmul (Zmul (Zneg Zone) x) y) (Zneg (Zmul x y)) := by
    exact zLaws.eq_trans
      (zLaws.mul_respects negOneMulX (zLaws.eq_refl y))
      (zMul_neg_left x y)
  calc
    zToInt (Zneg (Zmul x y)) =
        zToInt (Zmul (Zmul (Zneg Zone) x) y) :=
      zRelIff.mp (zLaws.eq_symm negMulXY)
    _ = zToInt (Zmul (Zneg Zone) x) * zToInt y :=
      zToInt_mul (Zmul (Zneg Zone) x) y
    _ = (zToInt (Zneg Zone) * zToInt x) * zToInt y := by
      rw [zToInt_mul]
    _ = ((-zToInt Zone) * zToInt x) * zToInt y := by
      rw [zToInt_neg]
    _ = (-1 : _root_.Int) * zToInt x * zToInt y := by
      rw [zToInt_one]

def toGaussianInt (z : GaussInt) : _root_.GaussianInt :=
  ⟨zToInt z.re, zToInt z.im⟩

def ofGaussianInt (z : _root_.GaussianInt) : GaussInt :=
  { re := zOfInt z.re, im := zOfInt z.im }

theorem ofGaussianInt_toGaussianInt_rel (z : GaussInt) :
    GaussEq (ofGaussianInt (toGaussianInt z)) z := by
  constructor
  · exact zOfInt_zToInt_rel z.re
  · exact zOfInt_zToInt_rel z.im

theorem toGaussianInt_ofGaussianInt (z : _root_.GaussianInt) :
    toGaussianInt (ofGaussianInt z) = z := by
  cases z with
  | mk re im =>
      unfold toGaussianInt ofGaussianInt
      ext <;> exact zOfInt_toInt _

theorem gaussEq_iff_toGaussianInt_eq {z w : GaussInt} :
    GaussEq z w ↔ toGaussianInt z = toGaussianInt w := by
  constructor
  · intro h
    ext
    · exact zRelIff.mp h.left
    · exact zRelIff.mp h.right
  · intro h
    constructor
    · exact zRelIff.mpr (congrArg Zsqrtd.re h)
    · exact zRelIff.mpr (congrArg Zsqrtd.im h)

def IsCanonical (z : GaussInt) : Prop :=
  z = ofGaussianInt (toGaussianInt z)

def CGaussInt : Type :=
  {z : GaussInt // IsCanonical z}

def normalize (z : GaussInt) : CGaussInt :=
  ⟨ofGaussianInt (toGaussianInt z), by
    unfold IsCanonical
    rw [toGaussianInt_ofGaussianInt]⟩

def CGaussInt.ofGaussianInt (z : _root_.GaussianInt) : CGaussInt :=
  ⟨BedcMathlibBridge.Constructive.Gaussian.ofGaussianInt z, by
    unfold IsCanonical
    rw [BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_ofGaussianInt]⟩

def CGaussInt.toGaussianInt (z : CGaussInt) : _root_.GaussianInt :=
  BedcMathlibBridge.Constructive.Gaussian.toGaussianInt z.val

theorem CGaussInt.toGaussianInt_ofGaussianInt (z : _root_.GaussianInt) :
    (CGaussInt.ofGaussianInt z).toGaussianInt = z := by
  exact BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_ofGaussianInt z

theorem CGaussInt.ofGaussianInt_toGaussianInt (z : CGaussInt) :
    CGaussInt.ofGaussianInt z.toGaussianInt = z := by
  rcases z with ⟨z, canonical⟩
  apply Subtype.ext
  exact canonical.symm

theorem CGaussInt.canonical_ext {z w : CGaussInt}
    (h : z.toGaussianInt = w.toGaussianInt) : z = w := by
  calc
    z = CGaussInt.ofGaussianInt z.toGaussianInt := (CGaussInt.ofGaussianInt_toGaussianInt z).symm
    _ = CGaussInt.ofGaussianInt w.toGaussianInt := by rw [h]
    _ = w := CGaussInt.ofGaussianInt_toGaussianInt w

def zeroProvenanceAnchor : Unit :=
  let _ :
      BEDC.Derived.GaussianUp.gaussZero =
        BEDC.Derived.GaussianUp.gaussZero := rfl
  ()

def oneProvenanceAnchor : Unit :=
  let _ :
      BEDC.Derived.GaussianUp.gaussOne =
        BEDC.Derived.GaussianUp.gaussOne := rfl
  ()

def addProvenanceAnchor : Unit :=
  let _ :
      (∀ z w : GaussInt,
        BEDC.Derived.GaussianUp.gaussAdd z w =
          BEDC.Derived.GaussianUp.gaussAdd z w) :=
    fun _ _ => rfl
  ()

def negProvenanceAnchor : Unit :=
  let _ :
      (∀ z : GaussInt,
        BEDC.Derived.GaussianUp.gaussNeg z =
          BEDC.Derived.GaussianUp.gaussNeg z) :=
    fun _ => rfl
  ()

def mulProvenanceAnchor : Unit :=
  let _ :
      (∀ z w : GaussInt,
        BEDC.Derived.GaussianUp.gaussMul z w =
          BEDC.Derived.GaussianUp.gaussMul z w) :=
    fun _ _ => rfl
  ()

@[bedcDerived BEDC.Derived.GaussianUp.gaussZero]
instance instZeroCGaussInt : Zero CGaussInt where
  zero :=
    let _ := zeroProvenanceAnchor
    CGaussInt.ofGaussianInt 0

@[bedcDerived BEDC.Derived.GaussianUp.gaussOne]
instance instOneCGaussInt : One CGaussInt where
  one :=
    let _ := oneProvenanceAnchor
    CGaussInt.ofGaussianInt 1

@[bedcDerived BEDC.Derived.GaussianUp.gaussAdd]
instance instAddCGaussInt : Add CGaussInt where
  add z w :=
    let _ := addProvenanceAnchor
    normalize (gaussAdd z.val w.val)

@[bedcDerived BEDC.Derived.GaussianUp.gaussNeg]
instance instNegCGaussInt : Neg CGaussInt where
  neg z :=
    let _ := negProvenanceAnchor
    normalize (gaussNeg z.val)

@[bedcDerived BEDC.Derived.GaussianUp.gaussMul]
instance instMulCGaussInt : Mul CGaussInt where
  mul z w :=
    let _ := mulProvenanceAnchor
    normalize (gaussMul z.val w.val)

theorem toGaussianInt_zero : toGaussianInt gaussZero = 0 := by
  ext <;> exact zToInt_zero

theorem toGaussianInt_one : toGaussianInt gaussOne = 1 := by
  ext
  · exact zToInt_one
  · exact zToInt_zero

theorem toGaussianInt_add (z w : GaussInt) :
    toGaussianInt (gaussAdd z w) = toGaussianInt z + toGaussianInt w := by
  ext
  · exact zToInt_add z.re w.re
  · exact zToInt_add z.im w.im

theorem toGaussianInt_neg (z : GaussInt) :
    toGaussianInt (gaussNeg z) = -toGaussianInt z := by
  ext
  · exact zToInt_neg z.re
  · exact zToInt_neg z.im

theorem toGaussianInt_mul (z w : GaussInt) :
    toGaussianInt (gaussMul z w) = toGaussianInt z * toGaussianInt w := by
  ext
  · change
      zToInt (Zadd (Zmul z.re w.re) (Zneg (Zmul z.im w.im))) =
        (⟨zToInt z.re, zToInt z.im⟩ *
          ⟨zToInt w.re, zToInt w.im⟩ : _root_.GaussianInt).re
    rw [zToInt_add, zToInt_mul, zToInt_neg_mul]
    rw [Zsqrtd.re_mul]
  · change
      zToInt (Zadd (Zmul z.re w.im) (Zmul z.im w.re)) =
        (⟨zToInt z.re, zToInt z.im⟩ *
          ⟨zToInt w.re, zToInt w.im⟩ : _root_.GaussianInt).im
    rw [zToInt_add, zToInt_mul, zToInt_mul]
    rw [Zsqrtd.im_mul]

theorem CGaussInt.toGaussianInt_zero : (0 : CGaussInt).toGaussianInt = 0 := by
  exact CGaussInt.toGaussianInt_ofGaussianInt 0

theorem CGaussInt.toGaussianInt_one : (1 : CGaussInt).toGaussianInt = 1 := by
  exact CGaussInt.toGaussianInt_ofGaussianInt 1

theorem CGaussInt.toGaussianInt_add (z w : CGaussInt) :
    (z + w).toGaussianInt = z.toGaussianInt + w.toGaussianInt := by
  rcases z with ⟨z, _hz⟩
  rcases w with ⟨w, _hw⟩
  change BedcMathlibBridge.Constructive.Gaussian.toGaussianInt
      (BedcMathlibBridge.Constructive.Gaussian.ofGaussianInt
        (BedcMathlibBridge.Constructive.Gaussian.toGaussianInt (gaussAdd z w))) =
    BedcMathlibBridge.Constructive.Gaussian.toGaussianInt z +
      BedcMathlibBridge.Constructive.Gaussian.toGaussianInt w
  rw [BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_ofGaussianInt]
  exact BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_add z w

theorem CGaussInt.toGaussianInt_neg (z : CGaussInt) :
    (-z).toGaussianInt = -z.toGaussianInt := by
  rcases z with ⟨z, _hz⟩
  change BedcMathlibBridge.Constructive.Gaussian.toGaussianInt
      (BedcMathlibBridge.Constructive.Gaussian.ofGaussianInt
        (BedcMathlibBridge.Constructive.Gaussian.toGaussianInt (gaussNeg z))) =
    -BedcMathlibBridge.Constructive.Gaussian.toGaussianInt z
  rw [BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_ofGaussianInt]
  exact BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_neg z

theorem CGaussInt.toGaussianInt_mul (z w : CGaussInt) :
    (z * w).toGaussianInt = z.toGaussianInt * w.toGaussianInt := by
  rcases z with ⟨z, _hz⟩
  rcases w with ⟨w, _hw⟩
  change BedcMathlibBridge.Constructive.Gaussian.toGaussianInt
      (BedcMathlibBridge.Constructive.Gaussian.ofGaussianInt
        (BedcMathlibBridge.Constructive.Gaussian.toGaussianInt (gaussMul z w))) =
    BedcMathlibBridge.Constructive.Gaussian.toGaussianInt z *
      BedcMathlibBridge.Constructive.Gaussian.toGaussianInt w
  rw [BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_ofGaussianInt]
  exact BedcMathlibBridge.Constructive.Gaussian.toGaussianInt_mul z w

theorem CGaussInt.gaussEq_iff_toGaussianInt_eq (z w : CGaussInt) :
    GaussEq z.val w.val ↔ z.toGaussianInt = w.toGaussianInt :=
  BedcMathlibBridge.Constructive.Gaussian.gaussEq_iff_toGaussianInt_eq

def CGaussInt.toGaussianIntEquiv : CGaussInt ≃ _root_.GaussianInt where
  toFun := CGaussInt.toGaussianInt
  invFun := CGaussInt.ofGaussianInt
  left_inv := CGaussInt.ofGaussianInt_toGaussianInt
  right_inv := CGaussInt.toGaussianInt_ofGaussianInt

def CGaussInt.toGaussianIntAddEquiv : CGaussInt ≃+ _root_.GaussianInt :=
  AddEquiv.mk CGaussInt.toGaussianIntEquiv CGaussInt.toGaussianInt_add

def CGaussInt.toGaussianIntRingEquiv : CGaussInt ≃+* _root_.GaussianInt :=
  RingEquiv.mk
    CGaussInt.toGaussianIntEquiv
    CGaussInt.toGaussianInt_mul
    CGaussInt.toGaussianInt_add

end BedcMathlibBridge.Constructive.Gaussian
