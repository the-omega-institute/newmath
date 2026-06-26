import BEDC.Algebra.Rel.GaussianUp
import BEDC.Derived.RHRoute.UnitaryBalance

namespace BEDC.Derived.RHRoute.FunctionalEquationSymmetry

open BEDC.Derived.RationalUp

abbrev RatNum := BEDC.Derived.RationalUp.RatNum

def ratHalf : RatNum :=
  BEDC.Derived.BernoulliUp.ratOfIntOverNat 1 1

structure SignedRat where
  pos : RatNum
  neg : RatNum

def SignedRatEq (x y : SignedRat) : Prop :=
  RatEq x.pos y.pos ∧ RatEq x.neg y.neg

def signedRatZero : SignedRat where
  pos := ratZero
  neg := ratZero

def signedRatNeg (x : SignedRat) : SignedRat where
  pos := x.neg
  neg := x.pos

def SignedRatIsZero (x : SignedRat) : Prop :=
  RatEq x.pos x.neg

theorem SignedRatEq_refl (x : SignedRat) :
    SignedRatEq x x := by
  exact And.intro (RatEq_refl x.pos) (RatEq_refl x.neg)

theorem SignedRatEq_symm {x y : SignedRat} :
    SignedRatEq x y -> SignedRatEq y x := by
  intro h
  exact And.intro (RatEq_symm h.left) (RatEq_symm h.right)

theorem signedRatNeg_involutive (x : SignedRat) :
    SignedRatEq (signedRatNeg (signedRatNeg x)) x := by
  exact SignedRatEq_refl x

theorem signedRat_neg_fixed_iff_zero (x : SignedRat) :
    SignedRatEq (signedRatNeg x) x ↔ SignedRatIsZero x := by
  constructor
  · intro h
    exact RatEq_symm h.left
  · intro h
    exact And.intro (RatEq_symm h) h

structure RationalComplex where
  reAboveHalf : RatNum
  reBelowHalf : RatNum
  im : SignedRat

def ComplexEq (z w : RationalComplex) : Prop :=
  RatEq z.reAboveHalf w.reAboveHalf ∧
    RatEq z.reBelowHalf w.reBelowHalf ∧
      SignedRatEq z.im w.im

theorem ComplexEq_refl (z : RationalComplex) :
    ComplexEq z z := by
  exact And.intro (RatEq_refl z.reAboveHalf)
    (And.intro (RatEq_refl z.reBelowHalf) (SignedRatEq_refl z.im))

theorem ComplexEq_symm {z w : RationalComplex} :
    ComplexEq z w -> ComplexEq w z := by
  intro h
  exact And.intro (RatEq_symm h.left)
    (And.intro (RatEq_symm h.right.left) (SignedRatEq_symm h.right.right))

def complexConj (z : RationalComplex) : RationalComplex where
  reAboveHalf := z.reAboveHalf
  reBelowHalf := z.reBelowHalf
  im := signedRatNeg z.im

def oneMinus (z : RationalComplex) : RationalComplex where
  reAboveHalf := z.reBelowHalf
  reBelowHalf := z.reAboveHalf
  im := signedRatNeg z.im

def reflectJ (z : RationalComplex) : RationalComplex where
  reAboveHalf := z.reBelowHalf
  reBelowHalf := z.reAboveHalf
  im := z.im

theorem reflectJ_eq_oneMinus_conj (z : RationalComplex) :
    ComplexEq (reflectJ z) (oneMinus (complexConj z)) := by
  exact ComplexEq_refl (reflectJ z)

theorem reflectJ_involutive (z : RationalComplex) :
    ComplexEq (reflectJ (reflectJ z)) z := by
  exact ComplexEq_refl z

def ReEqHalf (z : RationalComplex) : Prop :=
  RatEq z.reAboveHalf z.reBelowHalf

def JFixed (z : RationalComplex) : Prop :=
  ComplexEq (reflectJ z) z

def CriticalLine (z : RationalComplex) : Prop :=
  ReEqHalf z

theorem J_fixed_iff_re_half (z : RationalComplex) :
    JFixed z ↔ ReEqHalf z := by
  constructor
  · intro h
    exact RatEq_symm h.left
  · intro h
    exact And.intro (RatEq_symm h)
      (And.intro h (SignedRatEq_refl z.im))

theorem criticalLine_J_fixed_iff (z : RationalComplex) :
    JFixed z ↔ CriticalLine z :=
  J_fixed_iff_re_half z

theorem criticalLine_re_half_iff (z : RationalComplex) :
    CriticalLine z ↔ ReEqHalf z := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

def symmetryOrbit (z : RationalComplex) : List RationalComplex :=
  [z, complexConj z, oneMinus z, reflectJ z]

def JOrbitCollapses (z : RationalComplex) : Prop :=
  ComplexEq (reflectJ z) z

theorem orbit_on_critical_line_iff (z : RationalComplex) :
    JOrbitCollapses z ↔ CriticalLine z :=
  J_fixed_iff_re_half z

def ImaginaryOnRealAxis (z : RationalComplex) : Prop :=
  SignedRatIsZero z.im

def SymmetryOrbitSingleton (z : RationalComplex) : Prop :=
  ∀ {w : RationalComplex}, w ∈ symmetryOrbit z -> ComplexEq w z

theorem complexConj_fixed_iff_real_axis (z : RationalComplex) :
    ComplexEq (complexConj z) z ↔ ImaginaryOnRealAxis z := by
  constructor
  · intro h
    exact (signedRat_neg_fixed_iff_zero z.im).mp h.right.right
  · intro h
    exact And.intro (RatEq_refl z.reAboveHalf)
      (And.intro (RatEq_refl z.reBelowHalf)
        ((signedRat_neg_fixed_iff_zero z.im).mpr h))

theorem oneMinus_fixed_from_critical_and_real_axis (z : RationalComplex) :
    CriticalLine z -> ImaginaryOnRealAxis z -> ComplexEq (oneMinus z) z := by
  intro critical realAxis
  exact And.intro (RatEq_symm critical)
    (And.intro critical ((signedRat_neg_fixed_iff_zero z.im).mpr realAxis))

theorem symmetryOrbit_singleton_iff_criticalLine_and_real_axis
    (z : RationalComplex) :
    SymmetryOrbitSingleton z ↔ CriticalLine z ∧ ImaginaryOnRealAxis z := by
  constructor
  · intro orbitSingle
    have jMember : reflectJ z ∈ symmetryOrbit z := by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head [])))
    have conjMember : complexConj z ∈ symmetryOrbit z := by
      exact List.Mem.tail _ (List.Mem.head _)
    have fixedJ : JFixed z :=
      orbitSingle jMember
    have fixedConj : ComplexEq (complexConj z) z :=
      orbitSingle conjMember
    exact And.intro ((J_fixed_iff_re_half z).mp fixedJ)
      ((complexConj_fixed_iff_real_axis z).mp fixedConj)
  · intro h
    intro w member
    cases member with
    | head =>
        exact ComplexEq_refl z
    | tail _ memberTail =>
        cases memberTail with
        | head =>
            exact (complexConj_fixed_iff_real_axis z).mpr h.right
        | tail _ memberTailTail =>
            cases memberTailTail with
            | head =>
                exact oneMinus_fixed_from_critical_and_real_axis z h.left h.right
            | tail _ memberLast =>
                cases memberLast with
                | head =>
                    exact (J_fixed_iff_re_half z).mpr h.left
                | tail _ memberNil =>
                    cases memberNil

theorem criticalLine_fixed_set_triple_equiv
    (z : RationalComplex) :
    (CriticalLine z ↔ ReEqHalf z) ∧
      (ReEqHalf z ↔ JFixed z) := by
  exact And.intro (criticalLine_re_half_iff z)
    (Iff.symm (J_fixed_iff_re_half z))

theorem unitaryBalance_surface_norm_one
    (surface : BEDC.Derived.RHRoute.UnitaryBalance.UnitaryBalanceSurface) :
    RatEq
      (BEDC.Derived.RHRoute.UnitaryBalance.squaredNormOnWindow surface.channel)
      ratOne :=
  surface.norm_one

end BEDC.Derived.RHRoute.FunctionalEquationSymmetry
