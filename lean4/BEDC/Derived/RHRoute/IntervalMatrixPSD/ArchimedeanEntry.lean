import BEDC.Derived.RHRoute.IntervalMatrixPSD.PolynomialIntegral

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.LocatedReal
open BEDC.Real.RatNumKernel

abbrev ArchPoly : Type :=
  List BRat

def inClosedPanel (a b t : BRat) : Prop :=
  ratLe a t ∧ ratLe t b

def ZeroChamberSquareIdentity
    (S : BRat -> BRat) (Hpoly : ArchPoly) (a b : BRat) : Prop :=
  ∀ t, inClosedPanel a b t ->
    RatEq (S t) (ratMul (ratMul t t) (evalPoly Hpoly t))

def polyAdd : ArchPoly -> ArchPoly -> ArchPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => ratAdd a b :: polyAdd as bs

def polyScale (c : BRat) : ArchPoly -> ArchPoly
  | [] => []
  | a :: as => ratMul c a :: polyScale c as

def polyShift (p : ArchPoly) : ArchPoly :=
  ratZero :: p

def polyMul : ArchPoly -> ArchPoly -> ArchPoly
  | [], _ => []
  | a :: as, q => polyAdd (polyScale a q) (polyShift (polyMul as q))

def zeroPanelApoly (Hpoly : ArchPoly) : ArchPoly :=
  polyShift Hpoly

def PolyAbsBoundSound (Apoly : ArchPoly) (a b BA : BRat) : Prop :=
  ∀ t, inClosedPanel a b t -> ratLe (ratAbs (evalPoly Apoly t)) BA

structure KernelApprox (K : BRat -> BRat) (a b : BRat) where
  T : ArchPoly
  eps : BRat
  eps_nonneg : ratLe ratZero eps
  sound :
    ∀ t, inClosedPanel a b t ->
      ratLe (ratAbs (ratSub (K t) (evalPoly T t))) eps

def zeroPanelPolynomial
    (F0 : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat} {a b : BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) : ArchPoly :=
  polyAdd
    (polyMul (zeroPanelApoly Hpoly) K1Approx.T)
    (polyScale F0 K0Approx.T)

def zeroPanelPolynomialModel
    (F0 : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat} {a b : BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (t : BRat) : BRat :=
  ratAdd
    (ratMul (evalPoly (zeroPanelApoly Hpoly) t)
      (evalPoly K1Approx.T t))
    (ratMul F0 (evalPoly K0Approx.T t))

def zeroPanelDesingularizedIntegrand
    (F0 : BRat) (Hpoly : ArchPoly)
    (K1 K0 : BRat -> BRat) (t : BRat) : BRat :=
  ratAdd
    (ratMul (evalPoly (zeroPanelApoly Hpoly) t) (K1 t))
    (ratMul F0 (K0 t))

def zeroPanelKernelResidual
    (F0 : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat} {a b : BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (t : BRat) : BRat :=
  ratAdd
    (ratMul (evalPoly (zeroPanelApoly Hpoly) t)
      (ratSub (K1 t) (evalPoly K1Approx.T t)))
    (ratMul F0 (ratSub (K0 t) (evalPoly K0Approx.T t)))

def archZeroPanelError
    (F0 BA : BRat) {K1 K0 : BRat -> BRat} {a b : BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) : BRat :=
  ratAdd
    (ratMul BA K1Approx.eps)
    (ratMul (ratAbs F0) K0Approx.eps)

def archZeroPanelRadius
    (a b F0 BA : BRat) {K1 K0 : BRat -> BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) : BRat :=
  ratMul (ratSub b a) (archZeroPanelError F0 BA K1Approx K0Approx)

def polyIntegralExact (P : ArchPoly) (a b : BRat) : BRat :=
  polyIntegralGap P a b

def intervalAround (center radius : BRat) : QInterval :=
  { lo := ratSub center radius
    hi := ratAdd center radius }

def archZeroPanelFromKernelApprox
    (a b F0 BA : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) : QInterval :=
  intervalAround
    (polyIntegralExact
      (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b)
    (archZeroPanelRadius a b F0 BA K1Approx K0Approx)

def ZeroPanelPointwiseApproxOnPanel
    (a b F0 BA : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) : Prop :=
  ∀ t, inClosedPanel a b t ->
    ratLe
      (ratAbs
        (ratSub
          (zeroPanelDesingularizedIntegrand F0 Hpoly K1 K0 t)
          (zeroPanelPolynomialModel F0 Hpoly K1Approx K0Approx t)))
      (archZeroPanelError F0 BA K1Approx K0Approx)

structure ZeroPanelArchContribution
    (a b F0 BA : BRat) (Hpoly : ArchPoly)
    (K1 K0 : BRat -> BRat)
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (hab : ratLe a b) where
  value : BRat
  enclosure_sound :
    ZeroPanelPointwiseApproxOnPanel a b F0 BA Hpoly K1Approx K0Approx ->
    LRealEq LocatedRatKit
      (polyRiemannIntegral
        (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b hab)
      (ratToLReal LocatedRatKit
        (polyIntegralExact
          (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b)) ->
    InInterval value
      (archZeroPanelFromKernelApprox a b F0 BA Hpoly K1Approx K0Approx)

def zeroPanelArchContribution
    {a b F0 BA : BRat} {Hpoly : ArchPoly}
    {K1 K0 : BRat -> BRat}
    {K1Approx : KernelApprox K1 a b}
    {K0Approx : KernelApprox K0 a b}
    {hab : ratLe a b}
    (C : ZeroPanelArchContribution a b F0 BA Hpoly K1 K0
      K1Approx K0Approx hab) : BRat :=
  C.value

private theorem ratMul_zero_right_local (x : BRat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_neg_right_local (x y : BRat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratNeg_nonneg_of_nonpos_local {x : BRat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _)
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x) subNonneg

private theorem ratAbs_eq_self_of_nonneg_local {x : BRat} :
    ratLe ratZero x -> RatEq (ratAbs x) x := by
  intro h
  unfold ratAbs
  exact ratMagnitude_eq_self_of_nonneg h

private theorem ratAbs_neg_local (x : BRat) :
    RatEq (ratAbs (ratNeg x)) (ratAbs x) := by
  unfold ratAbs
  exact ratMagnitude_neg x

private theorem ratSub_mul_left (c a b : BRat) :
    RatEq (ratMul c (ratSub a b))
      (ratSub (ratMul c a) (ratMul c b)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left c a (ratNeg b))
    (ratAdd_respects (RatEq_refl (ratMul c a))
      (ratMul_neg_right_local c b))

private theorem ratSub_add_add_common (x x' y y' : BRat) :
    RatEq (ratSub (ratAdd x y) (ratAdd x' y'))
      (ratAdd (ratSub x x') (ratSub y y')) := by
  unfold ratSub
  have negExpand :
      RatEq
        (ratAdd (ratAdd x y) (ratNeg (ratAdd x' y')))
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg y'))) :=
    ratAdd_respects (RatEq_refl _)
      (BEDC.Derived.LocatedReal.ratNeg_add_dist_local x' y')
  have regroup :
      RatEq
        (ratAdd (ratAdd x y) (ratAdd (ratNeg x') (ratNeg y')))
        (ratAdd (ratAdd x (ratNeg x')) (ratAdd y (ratNeg y'))) := by
    exact RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y
        (ratAdd (ratNeg x') (ratNeg y')))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x)
          (RatEq_symm
            (BEDC.Derived.LocatedReal.ratAdd_assoc_local y
              (ratNeg x') (ratNeg y'))))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (ratAdd_respects (ratAdd_comm y (ratNeg x'))
              (RatEq_refl (ratNeg y'))))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x)
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                (ratNeg x') y (ratNeg y')))
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg x')
                (ratAdd y (ratNeg y')))))))
  exact RatEq_trans _ _ _ negExpand regroup

private theorem zeroPanelResidual_eq_difference
    (F0 : BRat) (Hpoly : ArchPoly)
    {K1 K0 : BRat -> BRat} {a b : BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (t : BRat) :
    RatEq
      (ratSub
        (zeroPanelDesingularizedIntegrand F0 Hpoly K1 K0 t)
        (zeroPanelPolynomialModel F0 Hpoly K1Approx K0Approx t))
      (zeroPanelKernelResidual F0 Hpoly K1Approx K0Approx t) := by
  unfold zeroPanelDesingularizedIntegrand
  unfold zeroPanelPolynomialModel
  unfold zeroPanelKernelResidual
  exact RatEq_trans _ _ _
    (ratSub_add_add_common
      (ratMul (evalPoly (zeroPanelApoly Hpoly) t) (K1 t))
      (ratMul (evalPoly (zeroPanelApoly Hpoly) t)
        (evalPoly K1Approx.T t))
      (ratMul F0 (K0 t))
      (ratMul F0 (evalPoly K0Approx.T t)))
    (ratAdd_respects
      (RatEq_symm
        (ratSub_mul_left (evalPoly (zeroPanelApoly Hpoly) t)
          (K1 t) (evalPoly K1Approx.T t)))
      (RatEq_symm
        (ratSub_mul_left F0 (K0 t) (evalPoly K0Approx.T t))))

private theorem ratAbs_eq_neg_of_nonpos_local {x : BRat} :
    ratLe x ratZero -> RatEq (ratAbs x) (ratNeg x) := by
  intro h
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAbs_neg_local x))
    (ratAbs_eq_self_of_nonneg_local
      (ratNeg_nonneg_of_nonpos_local h))

private theorem ratAbs_nonneg_left_mul_le {a x bound : BRat}
    (ha : ratLe ratZero a)
    (hx : ratLe (ratAbs x) bound) :
    ratLe (ratAbs (ratMul a x)) (ratMul a bound) := by
  cases ratLe_total ratZero x with
  | inl hxNonneg =>
      have axNonneg : ratLe ratZero (ratMul a x) :=
        ratMul_nonneg ha hxNonneg
      have absEq : RatEq (ratAbs (ratMul a x)) (ratMul a x) :=
        ratAbs_eq_self_of_nonneg_local axNonneg
      have xToAbs : ratLe x (ratAbs x) :=
        BEDC.Derived.LocatedReal.ratLe_self_abs x
      have xToBound : ratLe x bound := ratLe_trans xToAbs hx
      have raw : ratLe (ratMul a x) (ratMul a bound) :=
        ratMul_le_mul_left xToBound ha
      exact ratLe_respects (RatEq_symm absEq) (RatEq_refl _) raw
  | inr hxNonpos =>
      have prodNonpos : ratLe (ratMul a x) ratZero := by
        have raw : ratLe (ratMul a x) (ratMul a ratZero) :=
          ratMul_le_mul_left hxNonpos ha
        exact ratLe_respects (RatEq_refl _)
          (ratMul_zero_right_local a) raw
      have absEq : RatEq (ratAbs (ratMul a x)) (ratNeg (ratMul a x)) :=
        ratAbs_eq_neg_of_nonpos_local prodNonpos
      have negXToAbs : ratLe (ratNeg x) (ratAbs x) :=
        BEDC.Derived.LocatedReal.ratLe_neg_abs x
      have negXToBound : ratLe (ratNeg x) bound :=
        ratLe_trans negXToAbs hx
      have raw : ratLe (ratMul a (ratNeg x)) (ratMul a bound) :=
        ratMul_le_mul_left negXToBound ha
      have negProdEq : RatEq (ratMul a (ratNeg x)) (ratNeg (ratMul a x)) :=
        ratMul_neg_right_local a x
      exact ratLe_respects (RatEq_symm absEq) (RatEq_refl _)
        (ratLe_respects negProdEq (RatEq_refl _) raw)

private theorem ratAbs_nonneg_right_mul_le {x a bound : BRat}
    (ha : ratLe ratZero a)
    (hx : ratLe (ratAbs x) bound) :
    ratLe (ratAbs (ratMul x a)) (ratMul bound a) := by
  have left :=
    ratAbs_nonneg_left_mul_le (a := a) (x := x) (bound := bound) ha hx
  exact ratLe_respects
    (BEDC.Derived.LocatedReal.ratAbs_respects (RatEq_symm (ratMul_comm x a)))
    (ratMul_comm a bound)
    left

theorem ratAbs_mul_le {x y bx boundY : BRat}
    (hx : ratLe (ratAbs x) bx)
    (hy : ratLe (ratAbs y) boundY) :
    ratLe (ratAbs (ratMul x y)) (ratMul bx boundY) := by
  have bxNonneg : ratLe ratZero bx :=
    ratLe_trans (ratMagnitude_nonneg x) hx
  cases ratLe_total ratZero y with
  | inl yNonneg =>
      have first :
          ratLe (ratAbs (ratMul x y)) (ratMul bx y) :=
        ratAbs_nonneg_right_mul_le
          (a := y) (x := x) (bound := bx) yNonneg hx
      have yToBound : ratLe y boundY :=
        ratLe_trans (BEDC.Derived.LocatedReal.ratLe_self_abs y) hy
      have second :
          ratLe (ratMul bx y) (ratMul bx boundY) :=
        ratMul_le_mul_left yToBound bxNonneg
      exact ratLe_trans first second
  | inr yNonpos =>
      have negYNonneg : ratLe ratZero (ratNeg y) :=
        ratNeg_nonneg_of_nonpos_local yNonpos
      have first :
          ratLe (ratAbs (ratMul x (ratNeg y))) (ratMul bx (ratNeg y)) :=
        ratAbs_nonneg_right_mul_le
          (a := ratNeg y) (x := x) (bound := bx) negYNonneg hx
      have negYToBound : ratLe (ratNeg y) boundY :=
        ratLe_trans (BEDC.Derived.LocatedReal.ratLe_neg_abs y) hy
      have second :
          ratLe (ratMul bx (ratNeg y)) (ratMul bx boundY) :=
        ratMul_le_mul_left negYToBound bxNonneg
      have absBridge :
          RatEq (ratAbs (ratMul x (ratNeg y))) (ratAbs (ratMul x y)) := by
        exact RatEq_trans _ _ _
          (BEDC.Derived.LocatedReal.ratAbs_respects
            (ratMul_neg_right_local x y))
          (ratAbs_neg_local (ratMul x y))
      exact ratLe_respects absBridge (RatEq_refl _)
        (ratLe_trans first second)

private theorem ratAdd_nonneg_local {x y : BRat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw : ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

theorem archZeroPanelError_nonneg
    {a b F0 BA : BRat} {K1 K0 : BRat -> BRat}
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (hBA : ratLe ratZero BA) :
    ratLe ratZero (archZeroPanelError F0 BA K1Approx K0Approx) := by
  unfold archZeroPanelError
  apply ratAdd_nonneg_local
  · exact ratMul_nonneg hBA K1Approx.eps_nonneg
  · exact ratMul_nonneg (ratMagnitude_nonneg F0) K0Approx.eps_nonneg

theorem polyAbsBound_nonneg_of_left
    {Apoly : ArchPoly} {a b BA : BRat}
    (hab : ratLe a b)
    (hA : PolyAbsBoundSound Apoly a b BA) :
    ratLe ratZero BA := by
  exact ratLe_trans (ratMagnitude_nonneg (evalPoly Apoly a))
    (hA a (And.intro (ratLe_refl a) hab))

theorem archZeroPanelRadius_nonneg
    {a b F0 BA : BRat} {Hpoly : ArchPoly}
    {K1 K0 : BRat -> BRat}
    (hab : ratLe a b)
    (hA : PolyAbsBoundSound (zeroPanelApoly Hpoly) a b BA)
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) :
    ratLe ratZero
      (archZeroPanelRadius a b F0 BA K1Approx K0Approx) := by
  unfold archZeroPanelRadius
  exact ratMul_nonneg
    (ratSub_nonneg_of_le hab)
    (archZeroPanelError_nonneg K1Approx K0Approx
      (polyAbsBound_nonneg_of_left hab hA))

theorem archZeroPanelPointwiseApprox_bound
    {a b F0 BA : BRat} {Hpoly : ArchPoly}
    {K1 K0 : BRat -> BRat}
    (hA : PolyAbsBoundSound (zeroPanelApoly Hpoly) a b BA)
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b) :
    ZeroPanelPointwiseApproxOnPanel a b F0 BA Hpoly K1Approx K0Approx := by
  intro t ht
  have residualBound :
      ratLe
        (ratAbs (zeroPanelKernelResidual F0 Hpoly K1Approx K0Approx t))
        (archZeroPanelError F0 BA K1Approx K0Approx) := by
    unfold zeroPanelKernelResidual archZeroPanelError
    have hA_t : ratLe (ratAbs (evalPoly (zeroPanelApoly Hpoly) t)) BA :=
      hA t ht
    have hK1_t :
        ratLe
          (ratAbs (ratSub (K1 t) (evalPoly K1Approx.T t)))
          K1Approx.eps :=
      K1Approx.sound t ht
    have hK0_t :
        ratLe
          (ratAbs (ratSub (K0 t) (evalPoly K0Approx.T t)))
          K0Approx.eps :=
      K0Approx.sound t ht
    have firstTerm :
        ratLe
          (ratAbs
            (ratMul (evalPoly (zeroPanelApoly Hpoly) t)
              (ratSub (K1 t) (evalPoly K1Approx.T t))))
          (ratMul BA K1Approx.eps) :=
      ratAbs_mul_le hA_t hK1_t
    have secondTerm :
        ratLe
          (ratAbs
            (ratMul F0
              (ratSub (K0 t) (evalPoly K0Approx.T t))))
          (ratMul (ratAbs F0) K0Approx.eps) :=
      ratAbs_mul_le (ratLe_refl (ratAbs F0)) hK0_t
    exact ratLe_trans
      (BEDC.Derived.LocatedReal.ratAbs_triangle
        (ratMul (evalPoly (zeroPanelApoly Hpoly) t)
          (ratSub (K1 t) (evalPoly K1Approx.T t)))
        (ratMul F0
          (ratSub (K0 t) (evalPoly K0Approx.T t))))
      (ratAdd_le_add firstTerm secondTerm)
  exact ratLe_respects
    (RatEq_symm
      (BEDC.Derived.LocatedReal.ratAbs_respects
        (zeroPanelResidual_eq_difference F0 Hpoly
          K1Approx K0Approx t)))
    (RatEq_refl _)
    residualBound

theorem archZeroPanelFromKernelApprox_sound
    {S : BRat -> BRat}
    {a b F0 BA : BRat} {Hpoly : ArchPoly}
    {K1 K0 : BRat -> BRat}
    (hab : ratLe a b)
    (_hSquare : ZeroChamberSquareIdentity S Hpoly a b)
    (hA : PolyAbsBoundSound (zeroPanelApoly Hpoly) a b BA)
    (K1Approx : KernelApprox K1 a b)
    (K0Approx : KernelApprox K0 a b)
    (C : ZeroPanelArchContribution a b F0 BA Hpoly K1 K0
      K1Approx K0Approx hab) :
    InInterval (zeroPanelArchContribution C)
      (archZeroPanelFromKernelApprox a b F0 BA Hpoly K1Approx K0Approx) := by
  have pointwise :
      ZeroPanelPointwiseApproxOnPanel a b F0 BA Hpoly K1Approx K0Approx :=
    archZeroPanelPointwiseApprox_bound hA K1Approx K0Approx
  have exactPoly :
      LRealEq LocatedRatKit
        (polyRiemannIntegral
          (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b hab)
        (ratToLReal LocatedRatKit
          (polyIntegralExact
            (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b)) :=
    polyRiemannIntegral_eq_antideriv
      (zeroPanelPolynomial F0 Hpoly K1Approx K0Approx) a b hab
  exact C.enclosure_sound pointwise exactPoly

structure ArchConstCert (CInf : BRat) where
  interval : QInterval
  sound : InInterval CInf interval

def archConstEntryInterval {CInf : BRat}
    (F0 : BRat) (cert : ArchConstCert CInf) : QInterval :=
  intervalMul (singletonInterval F0) cert.interval

theorem archConstEntryInterval_sound {CInf F0 : BRat}
    (cert : ArchConstCert CInf) :
    InInterval (ratMul F0 CInf) (archConstEntryInterval F0 cert) := by
  unfold archConstEntryInterval
  exact intervalMul_encloses
    (And.intro (ratLe_refl F0) (ratLe_refl F0))
    cert.sound

inductive ArchimedeanEntryObligation where
  | kernelApproxK1
  | kernelApproxK0
  | archConstant
  | nonzeroPanel
  | analyticKernelIntegral

end BEDC.Derived.RHRoute.IntervalMatrixPSD
