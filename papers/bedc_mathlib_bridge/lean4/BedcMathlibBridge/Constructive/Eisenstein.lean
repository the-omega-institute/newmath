import BEDC.Derived.EisensteinUp
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Equiv
import BedcGate.Provenance
import BedcMathlibBridge.Constructive.Gaussian

namespace BedcMathlibBridge.Constructive.Eisenstein

open BEDC.Derived.EisensteinUp
open BedcMathlibBridge.Constructive.Gaussian

abbrev EisensteinInt : Type :=
  _root_.QuadraticAlgebra _root_.Int (-1 : _root_.Int) (-1 : _root_.Int)

def toEisensteinInt (z : EisInt) : EisensteinInt :=
  ⟨zToInt z.re, zToInt z.om⟩

def ofEisensteinInt (z : EisensteinInt) : EisInt :=
  { re := zOfInt z.re, om := zOfInt z.im }

theorem ofEisensteinInt_toEisensteinInt_rel (z : EisInt) :
    EisEq (ofEisensteinInt (toEisensteinInt z)) z := by
  constructor
  · exact zOfInt_zToInt_rel z.re
  · exact zOfInt_zToInt_rel z.om

theorem toEisensteinInt_ofEisensteinInt (z : EisensteinInt) :
    toEisensteinInt (ofEisensteinInt z) = z := by
  cases z with
  | mk re im =>
      unfold toEisensteinInt ofEisensteinInt
      ext <;> exact zOfInt_toInt _

theorem eisEq_iff_toEisensteinInt_eq {z w : EisInt} :
    EisEq z w ↔ toEisensteinInt z = toEisensteinInt w := by
  constructor
  · intro h
    ext
    · exact zRelIff.mp h.left
    · exact zRelIff.mp h.right
  · intro h
    constructor
    · exact zRelIff.mpr (congrArg _root_.QuadraticAlgebra.re h)
    · exact zRelIff.mpr (congrArg _root_.QuadraticAlgebra.im h)

def IsCanonical (z : EisInt) : Prop :=
  z = ofEisensteinInt (toEisensteinInt z)

def CEisInt : Type :=
  {z : EisInt // IsCanonical z}

def normalize (z : EisInt) : CEisInt :=
  ⟨ofEisensteinInt (toEisensteinInt z), by
    unfold IsCanonical
    rw [toEisensteinInt_ofEisensteinInt]⟩

def CEisInt.ofEisensteinInt (z : EisensteinInt) : CEisInt :=
  ⟨BedcMathlibBridge.Constructive.Eisenstein.ofEisensteinInt z, by
    unfold IsCanonical
    rw [BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_ofEisensteinInt]⟩

def CEisInt.toEisensteinInt (z : CEisInt) : EisensteinInt :=
  BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt z.val

theorem CEisInt.toEisensteinInt_ofEisensteinInt (z : EisensteinInt) :
    (CEisInt.ofEisensteinInt z).toEisensteinInt = z := by
  exact BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_ofEisensteinInt z

theorem CEisInt.ofEisensteinInt_toEisensteinInt (z : CEisInt) :
    CEisInt.ofEisensteinInt z.toEisensteinInt = z := by
  rcases z with ⟨z, canonical⟩
  apply Subtype.ext
  exact canonical.symm

theorem CEisInt.canonical_ext {z w : CEisInt}
    (h : z.toEisensteinInt = w.toEisensteinInt) : z = w := by
  calc
    z = CEisInt.ofEisensteinInt z.toEisensteinInt :=
      (CEisInt.ofEisensteinInt_toEisensteinInt z).symm
    _ = CEisInt.ofEisensteinInt w.toEisensteinInt := by rw [h]
    _ = w := CEisInt.ofEisensteinInt_toEisensteinInt w

def zeroProvenanceAnchor : Unit :=
  let _ :
      BEDC.Derived.EisensteinUp.eisZero =
        BEDC.Derived.EisensteinUp.eisZero := rfl
  ()

def oneProvenanceAnchor : Unit :=
  let _ :
      BEDC.Derived.EisensteinUp.eisOne =
        BEDC.Derived.EisensteinUp.eisOne := rfl
  ()

def omegaProvenanceAnchor : Unit :=
  let _ :
      BEDC.Derived.EisensteinUp.eisOmega =
        BEDC.Derived.EisensteinUp.eisOmega := rfl
  ()

def addProvenanceAnchor : Unit :=
  let _ :
      (∀ z w : EisInt,
        BEDC.Derived.EisensteinUp.eisAdd z w =
          BEDC.Derived.EisensteinUp.eisAdd z w) :=
    fun _ _ => rfl
  ()

def negProvenanceAnchor : Unit :=
  let _ :
      (∀ z : EisInt,
        BEDC.Derived.EisensteinUp.eisNeg z =
          BEDC.Derived.EisensteinUp.eisNeg z) :=
    fun _ => rfl
  ()

def mulProvenanceAnchor : Unit :=
  let _ :
      (∀ z w : EisInt,
        BEDC.Derived.EisensteinUp.eisMul z w =
          BEDC.Derived.EisensteinUp.eisMul z w) :=
    fun _ _ => rfl
  ()

@[bedcDerived BEDC.Derived.EisensteinUp.eisZero]
instance instZeroCEisInt : Zero CEisInt where
  zero :=
    let _ := zeroProvenanceAnchor
    normalize eisZero

@[bedcDerived BEDC.Derived.EisensteinUp.eisOne]
instance instOneCEisInt : One CEisInt where
  one :=
    let _ := oneProvenanceAnchor
    normalize eisOne

@[bedcDerived BEDC.Derived.EisensteinUp.eisOmega]
def CEisInt.omega : CEisInt :=
  let _ := omegaProvenanceAnchor
  normalize eisOmega

@[bedcDerived BEDC.Derived.EisensteinUp.eisAdd]
instance instAddCEisInt : Add CEisInt where
  add z w :=
    let _ := addProvenanceAnchor
    normalize (eisAdd z.val w.val)

@[bedcDerived BEDC.Derived.EisensteinUp.eisNeg]
instance instNegCEisInt : Neg CEisInt where
  neg z :=
    let _ := negProvenanceAnchor
    normalize (eisNeg z.val)

@[bedcDerived BEDC.Derived.EisensteinUp.eisMul]
instance instMulCEisInt : Mul CEisInt where
  mul z w :=
    let _ := mulProvenanceAnchor
    normalize (eisMul z.val w.val)

theorem toEisensteinInt_add (z w : EisInt) :
    toEisensteinInt (eisAdd z w) = toEisensteinInt z + toEisensteinInt w := by
  ext
  · exact zToInt_add z.re w.re
  · exact zToInt_add z.om w.om

theorem toEisensteinInt_neg (z : EisInt) :
    toEisensteinInt (eisNeg z) = -toEisensteinInt z := by
  ext
  · exact zToInt_neg z.re
  · exact zToInt_neg z.om

theorem toEisensteinInt_mul (z w : EisInt) :
    toEisensteinInt (eisMul z w) = toEisensteinInt z * toEisensteinInt w := by
  ext
  · change
      zToInt (Zadd (Zmul z.re w.re) (Zneg (Zmul z.om w.om))) =
        (⟨zToInt z.re, zToInt z.om⟩ *
          ⟨zToInt w.re, zToInt w.om⟩ : EisensteinInt).re
    rw [zToInt_add, zToInt_mul, zToInt_neg_mul]
    rw [_root_.QuadraticAlgebra.re_mul]
  · change
      zToInt
        (Zadd (Zadd (Zmul z.re w.om) (Zmul z.om w.re))
          (Zneg (Zmul z.om w.om))) =
        (⟨zToInt z.re, zToInt z.om⟩ *
          ⟨zToInt w.re, zToInt w.om⟩ : EisensteinInt).im
    rw [zToInt_add, zToInt_add, zToInt_mul, zToInt_mul, zToInt_neg_mul]
    rw [_root_.QuadraticAlgebra.im_mul]

theorem CEisInt.toEisensteinInt_add (z w : CEisInt) :
    (z + w).toEisensteinInt = z.toEisensteinInt + w.toEisensteinInt := by
  rcases z with ⟨z, _hz⟩
  rcases w with ⟨w, _hw⟩
  change BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt
      (BedcMathlibBridge.Constructive.Eisenstein.ofEisensteinInt
        (BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt (eisAdd z w))) =
    BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt z +
      BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt w
  rw [BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_ofEisensteinInt]
  exact BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_add z w

theorem CEisInt.toEisensteinInt_neg (z : CEisInt) :
    (-z).toEisensteinInt = -z.toEisensteinInt := by
  rcases z with ⟨z, _hz⟩
  change BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt
      (BedcMathlibBridge.Constructive.Eisenstein.ofEisensteinInt
        (BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt (eisNeg z))) =
    -BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt z
  rw [BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_ofEisensteinInt]
  exact BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_neg z

theorem CEisInt.toEisensteinInt_mul (z w : CEisInt) :
    (z * w).toEisensteinInt = z.toEisensteinInt * w.toEisensteinInt := by
  rcases z with ⟨z, _hz⟩
  rcases w with ⟨w, _hw⟩
  change BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt
      (BedcMathlibBridge.Constructive.Eisenstein.ofEisensteinInt
        (BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt (eisMul z w))) =
    BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt z *
      BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt w
  rw [BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_ofEisensteinInt]
  exact BedcMathlibBridge.Constructive.Eisenstein.toEisensteinInt_mul z w

theorem CEisInt.eisEq_iff_toEisensteinInt_eq (z w : CEisInt) :
    EisEq z.val w.val ↔ z.toEisensteinInt = w.toEisensteinInt :=
  BedcMathlibBridge.Constructive.Eisenstein.eisEq_iff_toEisensteinInt_eq

def CEisInt.toEisensteinIntEquiv : CEisInt ≃ EisensteinInt where
  toFun := CEisInt.toEisensteinInt
  invFun := CEisInt.ofEisensteinInt
  left_inv := CEisInt.ofEisensteinInt_toEisensteinInt
  right_inv := CEisInt.toEisensteinInt_ofEisensteinInt

def CEisInt.toEisensteinIntAddEquiv : CEisInt ≃+ EisensteinInt :=
  AddEquiv.mk CEisInt.toEisensteinIntEquiv CEisInt.toEisensteinInt_add

def CEisInt.toEisensteinIntRingEquiv : CEisInt ≃+* EisensteinInt :=
  RingEquiv.mk
    CEisInt.toEisensteinIntEquiv
    CEisInt.toEisensteinInt_mul
    CEisInt.toEisensteinInt_add

end BedcMathlibBridge.Constructive.Eisenstein
