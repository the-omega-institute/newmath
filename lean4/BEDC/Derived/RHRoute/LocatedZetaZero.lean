import BEDC.Derived.LocatedReal
import BEDC.Derived.RHRoute.ZetaBoxEvaluator
import BEDC.Derived.Sqrt2BisectionUp

namespace BEDC.Derived.RHRoute.LocatedZetaZero

open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

def dyad (n : Nat) : Rat :=
  dyadicRat n

def half : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 1 1

structure RatRect where
  reLo : Rat
  reHi : Rat
  imLo : Rat
  imHi : Rat
  hRe : ratLt reLo reHi
  hIm : ratLt imLo imHi

def RatRect.Subset (A B : RatRect) : Prop :=
  ratLe B.reLo A.reLo ∧ ratLe A.reHi B.reHi ∧
    ratLe B.imLo A.imLo ∧ ratLe A.imHi B.imHi

def RatRect.reWidth (R : RatRect) : Rat :=
  BEDC.Derived.RationalUp.ratSub R.reHi R.reLo

def RatRect.imWidth (R : RatRect) : Rat :=
  BEDC.Derived.RationalUp.ratSub R.imHi R.imLo

def RatRect.centerRe (R : RatRect) : Rat :=
  ratMul (ratAdd R.reLo R.reHi) half

def RatRect.centerIm (R : RatRect) : Rat :=
  ratMul (ratAdd R.imLo R.imHi) half

structure RatRectCenter where
  re : Rat
  im : Rat

def RatRect.center (R : RatRect) : RatRectCenter :=
  { re := R.centerRe
    im := R.centerIm }

def distQ (z w : RatRectCenter) : Rat :=
  ratAdd (ratDist z.re w.re) (ratDist z.im w.im)

def RatInInterval (q lo hi : Rat) : Prop :=
  ratLe lo q ∧ ratLe q hi

def RatBetweenEndpoints (a b q : Rat) : Prop :=
  (ratLe a q ∧ ratLe q b) ∨ (ratLe b q ∧ ratLe q a)

def ComplexInBox (z : RatComplex) (box : ComplexBox) : Prop :=
  RatInInterval z.re box.re.lo box.re.hi ∧
    RatInInterval z.im box.im.lo box.im.hi

def ComplexBoxSubset (inner outer : ComplexBox) : Prop :=
  ratLe outer.re.lo inner.re.lo ∧ ratLe inner.re.hi outer.re.hi ∧
    ratLe outer.im.lo inner.im.lo ∧ ratLe inner.im.hi outer.im.hi

def ComplexBoxExcludesZero (box : ComplexBox) : Prop :=
  ComplexInBox ratComplexZero box -> False

structure LocatedRealByIntervals where
  lo : Nat -> Rat
  hi : Nat -> Rat
  nested : forall n : Nat, ratLe (lo n) (lo (Nat.succ n)) ∧
    ratLe (hi (Nat.succ n)) (hi n)
  diam :
    forall n : Nat,
      ratLe (BEDC.Derived.RationalUp.ratSub (hi n) (lo n)) (dyad n)

structure CenterCauchyPayload (R : Nat -> RatRect) where
  bound :
    forall m n : Nat,
      ratLe (distQ ((R m).center) ((R n).center))
        (dyad (Nat.min m n))

structure LocatedComplex where
  R : Nat -> RatRect
  nested : forall n : Nat, (R (Nat.succ n)).Subset (R n)
  reDiam : forall n : Nat, ratLe ((R n).reWidth) (dyad n)
  imDiam : forall n : Nat, ratLe ((R n).imWidth) (dyad n)
  centerPayload : CenterCauchyPayload R

def LocatedComplex.re (loc : LocatedComplex) : LocatedRealByIntervals :=
  { lo := fun n => (loc.R n).reLo
    hi := fun n => (loc.R n).reHi
    nested := by
      intro n
      have h := loc.nested n
      exact ⟨h.left, h.right.left⟩
    diam := loc.reDiam }

def LocatedComplex.im (loc : LocatedComplex) : LocatedRealByIntervals :=
  { lo := fun n => (loc.R n).imLo
    hi := fun n => (loc.R n).imHi
    nested := by
      intro n
      have h := loc.nested n
      exact ⟨h.right.right.left, h.right.right.right⟩
    diam := loc.imDiam }

theorem centers_cauchy (loc : LocatedComplex) :
    forall m n : Nat,
      ratLe (distQ ((loc.R m).center) ((loc.R n).center))
        (dyad (Nat.min m n)) :=
  loc.centerPayload.bound

inductive RectSide : Type where
  | south
  | east
  | north
  | west

def RatRect.ContainsPoint (R : RatRect) (z : RatComplex) : Prop :=
  RatInInterval z.re R.reLo R.reHi ∧ RatInInterval z.im R.imLo R.imHi

def RatRect.OnSide (R : RatRect) : RectSide -> RatComplex -> Prop
  | RectSide.south, z => R.ContainsPoint z ∧ RatEq z.im R.imLo
  | RectSide.east, z => R.ContainsPoint z ∧ RatEq z.re R.reHi
  | RectSide.north, z => R.ContainsPoint z ∧ RatEq z.im R.imHi
  | RectSide.west, z => R.ContainsPoint z ∧ RatEq z.re R.reLo

structure BoundarySegment (R : RatRect) (side : RectSide) where
  start : RatComplex
  finish : RatComplex
  startOnSide : R.OnSide side start
  finishOnSide : R.OnSide side finish

def BoundarySegment.Contains {R : RatRect} {side : RectSide}
    (segment : BoundarySegment R side) (z : RatComplex) : Prop :=
  match side with
  | RectSide.south =>
      R.OnSide RectSide.south z ∧
        RatBetweenEndpoints segment.start.re segment.finish.re z.re
  | RectSide.east =>
      R.OnSide RectSide.east z ∧
        RatBetweenEndpoints segment.start.im segment.finish.im z.im
  | RectSide.north =>
      R.OnSide RectSide.north z ∧
        RatBetweenEndpoints segment.start.re segment.finish.re z.re
  | RectSide.west =>
      R.OnSide RectSide.west z ∧
        RatBetweenEndpoints segment.start.im segment.finish.im z.im

-- 边界证书只连接有限有理 tube 数据与 `concreteZetaBox`; 不声明辐角原理、
-- 内部零点存在性, 或 located 复数上的 ζ 等式。
structure ZetaBoundarySegmentApartCert
    (R : RatRect) (side : RectSide)
    (concreteZetaBox : RatComplex -> Nat -> ComplexBox)
    (precision : Nat) where
  segment : BoundarySegment R side
  tube : ComplexBox
  coversSide :
    forall z : RatComplex,
      R.OnSide side z -> segment.Contains z
  segmentEnclosed :
    forall z : RatComplex,
      segment.Contains z ->
        ComplexBoxSubset (concreteZetaBox z precision) tube
  tubeApartZero : ComplexBoxExcludesZero tube

theorem ZetaBoundarySegmentApartCert.sideEnclosed
    {R : RatRect} {side : RectSide}
    {concreteZetaBox : RatComplex -> Nat -> ComplexBox}
    {precision : Nat}
    (cert :
      ZetaBoundarySegmentApartCert R side concreteZetaBox precision)
    (z : RatComplex) :
    R.OnSide side z ->
      ComplexBoxSubset (concreteZetaBox z precision) cert.tube := by
  intro hz
  exact cert.segmentEnclosed z (cert.coversSide z hz)

structure ZetaBoundaryApartCert (R : RatRect) where
  precision : Nat
  contourSamples : List RatComplex
  concreteZetaBox :
    RatComplex -> Nat -> BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox
  south :
    ZetaBoundarySegmentApartCert R RectSide.south concreteZetaBox precision
  east :
    ZetaBoundarySegmentApartCert R RectSide.east concreteZetaBox precision
  north :
    ZetaBoundarySegmentApartCert R RectSide.north concreteZetaBox precision
  west :
    ZetaBoundarySegmentApartCert R RectSide.west concreteZetaBox precision

inductive WindingTurn : Type where
  | counterclockwise
  | clockwise
  | flat

def windingTurnValue : WindingTurn -> Int
  | WindingTurn.counterclockwise => 1
  | WindingTurn.clockwise => -1
  | WindingTurn.flat => 0

def computedWindingFromTurns : List WindingTurn -> Int
  | [] => 0
  | turn :: rest => windingTurnValue turn + computedWindingFromTurns rest

structure WindingCert (R : RatRect) (k : Int) where
  boundaryApart : ZetaBoundaryApartCert R
  turns : List WindingTurn
  windingEq : computedWindingFromTurns turns = k

abbrev ZetaRectIndexCert (R : RatRect) (k : Int) :=
  WindingCert R k

structure RefinementStep (R S : RatRect) where
  subset : S.Subset R
  shrinkRe :
    ratLe S.reWidth
      (ratMul R.reWidth half)
  shrinkIm :
    ratLe S.imWidth
      (ratMul R.imWidth half)
  childIndex : ZetaRectIndexCert S 1

structure ZetaIndexStream where
  R : Nat -> RatRect
  nested : forall n : Nat, (R (Nat.succ n)).Subset (R n)
  reDiam : forall n : Nat, ratLe ((R n).reWidth) (dyad n)
  imDiam : forall n : Nat, ratLe ((R n).imWidth) (dyad n)
  centerPayload : CenterCauchyPayload R
  idx : forall n : Nat, ZetaRectIndexCert (R n) 1

structure ZetaIndexPrefix (N : Nat) where
  R : Nat -> RatRect
  nested :
    forall n : Nat, n < N -> (R (Nat.succ n)).Subset (R n)
  reDiam :
    forall n : Nat, n <= N -> ratLe ((R n).reWidth) (dyad n)
  imDiam :
    forall n : Nat, n <= N -> ratLe ((R n).imWidth) (dyad n)
  centerPayload :
    forall m n : Nat, m <= N -> n <= N ->
      ratLe (distQ ((R m).center) ((R n).center))
        (dyad (Nat.min m n))
  idx : forall n : Nat, n <= N -> ZetaRectIndexCert (R n) 1

def ZetaIndexStream.located (stream : ZetaIndexStream) : LocatedComplex :=
  { R := stream.R
    nested := stream.nested
    reDiam := stream.reDiam
    imDiam := stream.imDiam
    centerPayload := stream.centerPayload }

structure LocatedZetaZero where
  loc : LocatedComplex
  indexOne : forall n : Nat, ZetaRectIndexCert (loc.R n) 1

def LocatedZetaZero.fromIndexStream
    (stream : ZetaIndexStream) : LocatedZetaZero :=
  { loc := stream.located
    indexOne := stream.idx }

def existsLocatedData (rho : LocatedZetaZero) :
    Sigma (fun loc : LocatedComplex =>
      forall n : Nat, ZetaRectIndexCert (loc.R n) 1) :=
  ⟨rho.loc, rho.indexOne⟩

def rhoNearReLo : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 1 2

def rhoNearReHi : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 3 2

def rhoNearImLo : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 14 0

def rhoNearImHi : Rat :=
  BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo 15 0

theorem rhoNear_reLo_lt_reHi :
    ratLt rhoNearReLo rhoNearReHi := by
  unfold rhoNearReLo rhoNearReHi ratLt intLtUp BEDC.Derived.IntUp.intLt
    BEDC.Derived.RationalUp.IntMul ratDenInt
    BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo intOfNat intToPair
    BEDC.Derived.RationalUp.intMul BEDC.Derived.IntUp.pairMul
    BEDC.Derived.RationalUp.pairToInt BEDC.Derived.RationalUp.pairSign
    BEDC.Derived.RationalUp.pairMagnitude
  decide

theorem rhoNear_imLo_lt_imHi :
    ratLt rhoNearImLo rhoNearImHi := by
  unfold rhoNearImLo rhoNearImHi ratLt intLtUp BEDC.Derived.IntUp.intLt
    BEDC.Derived.RationalUp.IntMul ratDenInt
    BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo intOfNat intToPair
    BEDC.Derived.RationalUp.intMul BEDC.Derived.IntUp.pairMul
    BEDC.Derived.RationalUp.pairToInt BEDC.Derived.RationalUp.pairSign
    BEDC.Derived.RationalUp.pairMagnitude
  decide

theorem rhoNear_reLo_pos :
    ratLt ratZero rhoNearReLo := by
  unfold rhoNearReLo ratZero ratLt intLtUp BEDC.Derived.IntUp.intLt
    BEDC.Derived.RationalUp.IntMul ratDenInt
    BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo intOfNat intToRat intToPair
    BEDC.Derived.RationalUp.intMul BEDC.Derived.IntUp.pairMul
    BEDC.Derived.RationalUp.pairToInt BEDC.Derived.RationalUp.pairSign
    BEDC.Derived.RationalUp.pairMagnitude
  decide

theorem rhoNear_reHi_lt_one :
    ratLt rhoNearReHi ratOne := by
  unfold rhoNearReHi ratOne ratLt intLtUp BEDC.Derived.IntUp.intLt
    BEDC.Derived.RationalUp.IntMul ratDenInt
    BEDC.Derived.Sqrt2BisectionUp.natOverPowTwo intOfNat intToRat intToPair
    BEDC.Derived.RationalUp.intMul BEDC.Derived.IntUp.pairMul
    BEDC.Derived.RationalUp.pairToInt BEDC.Derived.RationalUp.pairSign
    BEDC.Derived.RationalUp.pairMagnitude
  decide

def rho_near_14_1347_R0 : RatRect :=
  { reLo := rhoNearReLo
    reHi := rhoNearReHi
    imLo := rhoNearImLo
    imHi := rhoNearImHi
    hRe := rhoNear_reLo_lt_reHi
    hIm := rhoNear_imLo_lt_imHi }

theorem rho_near_14_1347_R0_strip :
    ratLt ratZero rho_near_14_1347_R0.reLo ∧
      ratLt rho_near_14_1347_R0.reHi ratOne := by
  exact ⟨rhoNear_reLo_pos, rhoNear_reHi_lt_one⟩

structure RhoNearWindowCert where
  rect : RatRect
  rect_eq :
    rect.reLo = rhoNearReLo ∧ rect.reHi = rhoNearReHi ∧
      rect.imLo = rhoNearImLo ∧ rect.imHi = rhoNearImHi
  inCriticalStrip : ratLt ratZero rect.reLo ∧ ratLt rect.reHi ratOne

def rho_near_14_1347_window_cert : RhoNearWindowCert :=
  { rect := rho_near_14_1347_R0
    rect_eq := ⟨rfl, rfl, rfl, rfl⟩
    inCriticalStrip := rho_near_14_1347_R0_strip }

structure RhoNearIndexPrefix (N : Nat) where
  data : ZetaIndexPrefix N
  startsAtR0 : ZetaIndexPrefix.R data 0 = rho_near_14_1347_R0

theorem located_complex_re_projection (loc : LocatedComplex) :
    (loc.re).lo = fun n => (loc.R n).reLo := by
  rfl

theorem located_complex_im_projection (loc : LocatedComplex) :
    (loc.im).hi = fun n => (loc.R n).imHi := by
  rfl

theorem zeta_index_stream_centers_cauchy (stream : ZetaIndexStream) :
    forall m n : Nat,
      ratLe (distQ ((stream.R m).center) ((stream.R n).center))
        (dyad (Nat.min m n)) :=
  centers_cauchy stream.located

end BEDC.Derived.RHRoute.LocatedZetaZero
