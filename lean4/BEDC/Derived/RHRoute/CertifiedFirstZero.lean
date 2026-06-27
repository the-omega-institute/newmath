import BEDC.Derived.RHRoute.ZetaZeroLocated
import BEDC.Derived.Sqrt2BisectionUp

namespace BEDC.Derived.RHRoute.CertifiedFirstZero

open BEDC.FKernel.Hist
open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator
open BEDC.Derived.RHRoute.BoxKernelConcrete
open BEDC.Derived.RHRoute.ZetaZeroLocated

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ZetaBoxEvaluator.RatComplex

def dyadicNatRat (n : Nat) : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo n 0

theorem dyadicNatRat_le_of_le {a b : Nat} :
    a ≤ b -> ratLe (dyadicNatRat a) (dyadicNatRat b) := by
  intro h
  exact BEDC.Derived.Sqrt2BisectionUp.ratLe_natOverPowTwo_of_le
    (k := 0) h

def natInterval (lo hi : Nat) (h : lo ≤ hi) : QInterval :=
  { lo := dyadicNatRat lo
    hi := dyadicNatRat hi
    valid := dyadicNatRat_le_of_le h }

def firstZeroSearchBox : ComplexBox :=
  { re := natInterval 0 1 (Nat.zero_le 1)
    im := natInterval 14 15 (by decide) }

def firstZeroSeedPoint : RatComplex :=
  { re := halfRat
    im := dyadicNatRat 14 }

def boxCornerSW (box : ComplexBox) : RatComplex :=
  { re := box.re.lo, im := box.im.lo }

def boxCornerSE (box : ComplexBox) : RatComplex :=
  { re := box.re.hi, im := box.im.lo }

def boxCornerNE (box : ComplexBox) : RatComplex :=
  { re := box.re.hi, im := box.im.hi }

def boxCornerNW (box : ComplexBox) : RatComplex :=
  { re := box.re.lo, im := box.im.hi }

def rectangleContour (box : ComplexBox) : List RatComplex :=
  [boxCornerSW box, boxCornerSE box, boxCornerNE box, boxCornerNW box,
    boxCornerSW box]

def firstZeroContourSamples : List RatComplex :=
  rectangleContour firstZeroSearchBox

-- 有限绕数账本只记录采样转向。真正的数值判定由证书字段给出,
-- 这里不把尚未登记的 Platt--Trudgian 计算伪造成定理。
inductive WindingTurn : Type where
  | counterclockwise
  | clockwise
  | flat
  deriving DecidableEq

def windingPositiveCount : List WindingTurn -> Nat
  | [] => 0
  | WindingTurn.counterclockwise :: rest =>
      Nat.succ (windingPositiveCount rest)
  | WindingTurn.clockwise :: rest => windingPositiveCount rest
  | WindingTurn.flat :: rest => windingPositiveCount rest

def windingNegativeCount : List WindingTurn -> Nat
  | [] => 0
  | WindingTurn.counterclockwise :: rest => windingNegativeCount rest
  | WindingTurn.clockwise :: rest =>
      Nat.succ (windingNegativeCount rest)
  | WindingTurn.flat :: rest => windingNegativeCount rest

def WindingOne (turns : List WindingTurn) : Prop :=
  windingPositiveCount turns = Nat.succ (windingNegativeCount turns)

structure RationalContourCertificate where
  box : ComplexBox
  samples : List RatComplex
  samples_readback : samples = rectangleContour box
  turns : List WindingTurn
  winding_one : WindingOne turns
  boundary_nonzero :
    ∀ z : RatComplex, z ∈ samples -> ZetaNonzeroLocated z

def firstZeroContourCertificateShape
    (cert : RationalContourCertificate) : Prop :=
  cert.box = firstZeroSearchBox ∧
    cert.samples = firstZeroContourSamples ∧
      WindingOne cert.turns

def RatIntervalSubset (inner outer : QInterval) : Prop :=
  ratLe outer.lo inner.lo ∧ ratLe inner.hi outer.hi

def ComplexBoxSubset (inner outer : ComplexBox) : Prop :=
  RatIntervalSubset inner.re outer.re ∧ RatIntervalSubset inner.im outer.im

def BoxStreamNested (boxes : Nat -> ComplexBox) : Prop :=
  ∀ k : Nat, ComplexBoxSubset (boxes (Nat.succ k)) (boxes k)

def dyadicUnit (k : Nat) : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 1 k

def BoxDiameterBound (box : ComplexBox) (k : Nat) : Prop :=
  ratLe
      (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub
        box.re.hi box.re.lo)
      (dyadicUnit k) ∧
    ratLe
      (BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratSub
        box.im.hi box.im.lo)
      (dyadicUnit k)

def BoxStreamDiametersShrink (boxes : Nat -> ComplexBox) : Prop :=
  ∀ k : Nat, BoxDiameterBound (boxes k) k

structure CertifiedZeroIsolation where
  point : RatComplex
  input : ConcreteZetaLocatedInput
  point_eq : input.point = point
  seed_box : ComplexBox
  seed_box_is_search : seed_box = firstZeroSearchBox
  contour : RationalContourCertificate
  contour_box : contour.box = seed_box
  contour_samples : contour.samples = rectangleContour contour.box
  boxes : Nat -> ComplexBox
  boxes_zero : boxes 0 = seed_box
  nested : BoxStreamNested boxes
  diameter_bound : BoxStreamDiametersShrink boxes
  point_in_boxes : ∀ k : Nat, ComplexInBox point (boxes k)
  zeta_boxes_contain_zero :
    ∀ precision : Nat,
      ComplexInBox complexZero (concreteZetaBox input precision)

def CertifiedZeroIsolation.located
    (cert : CertifiedZeroIsolation) : ZetaZeroLocated cert.point :=
  Exists.intro cert.input
    (And.intro cert.point_eq cert.zeta_boxes_contain_zero)

theorem CertifiedZeroIsolation.point_in_search_box
    (cert : CertifiedZeroIsolation) :
    ComplexInBox cert.point firstZeroSearchBox := by
  have hbox : ComplexInBox cert.point (cert.boxes 0) :=
    cert.point_in_boxes 0
  rw [cert.boxes_zero, cert.seed_box_is_search] at hbox
  exact hbox

theorem first_zeta_zero_constructible
    (cert : CertifiedZeroIsolation) :
    ∃ s : RatComplex,
      ZetaZeroLocated s ∧
        ComplexInBox s firstZeroSearchBox ∧
          WindingOne cert.contour.turns ∧
            BoxStreamNested cert.boxes ∧
              BoxStreamDiametersShrink cert.boxes ∧
                (∀ z : RatComplex,
                  z ∈ cert.contour.samples -> ZetaNonzeroLocated z) := by
  exact Exists.intro cert.point
    (And.intro (CertifiedZeroIsolation.located cert)
      (And.intro (CertifiedZeroIsolation.point_in_search_box cert)
        (And.intro cert.contour.winding_one
          (And.intro cert.nested
            (And.intro cert.diameter_bound cert.contour.boundary_nonzero)))))

theorem first_zeta_zero_precision_box
    (cert : CertifiedZeroIsolation) (precision : Nat) :
    ∃ input : ConcreteZetaLocatedInput,
      input.point = cert.point ∧
        ComplexInBox complexZero (concreteZetaBox input precision) := by
  exact zetaZeroLocated_at (CertifiedZeroIsolation.located cert) precision

end BEDC.Derived.RHRoute.CertifiedFirstZero
