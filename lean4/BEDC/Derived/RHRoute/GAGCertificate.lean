import BEDC.Derived.RationalUp

namespace BEDC.Derived.RHRoute.GAGCertificate

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp

abbrev BRat : Type :=
  RatNum

private abbrev RatInt : Type :=
  BEDC.Derived.PrimeUp.IntegerUp

private theorem ratEq_zero_of_num_zero_local {x : BRat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem intAdd_four_swap_local (a b c d : RatInt) :
    IntEq (IntAdd (IntAdd a b) (IntAdd c d))
      (IntAdd (IntAdd a c) (IntAdd b d)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  exact R.trans (R.add_assoc a b (IntAdd c d))
    (R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc b c d)))
      (R.trans
        (R.add_congr (R.refl a)
          (R.add_congr (R.add_comm b c) (R.refl d)))
        (R.trans
          (R.add_congr (R.refl a) (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (IntAdd b d))))))

private theorem intNeg_add_local (a b : RatInt) :
    IntEq (IntNeg (IntAdd a b)) (IntAdd (IntNeg a) (IntNeg b)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  have paired :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b)))
        (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b))) :=
    intAdd_four_swap_local a b (IntNeg a) (IntNeg b)
  have collapsed :
      IntEq (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b)))
        (IntAdd intZero intZero) :=
    IntAdd_respects (IntAdd_neg a) (IntAdd_neg b)
  have zeroed :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b))) intZero :=
    IntEq_trans paired (IntEq_trans collapsed (IntAdd_zero_left intZero))
  exact IntEq_symm
    (R.eq_neg_of_add_eq_zero (a := IntAdd a b)
      (b := IntAdd (IntNeg a) (IntNeg b)) zeroed)

private theorem ratDenInt_neg_local (x : BRat) :
    IntEq (ratDenInt (ratNeg x)) (ratDenInt x) := by
  unfold ratDenInt ratNeg
  exact IntEq_refl (intOfNat x.den (ratDenCarrier x))

private theorem intRatAddAssocNum_local
    (xn xd yn yd zn zd : RatInt) :
    IntEq
      (IntAdd
        (IntMul (IntAdd (IntMul xn yd) (IntMul yn xd)) zd)
        (IntMul zn (IntMul xd yd)))
      (IntAdd
        (IntMul xn (IntMul yd zd))
        (IntMul (IntAdd (IntMul yn zd) (IntMul zn yd)) xd)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  let A := IntMul (IntMul xn yd) zd
  let B := IntMul (IntMul yn xd) zd
  let C := IntMul zn (IntMul xd yd)
  let A' := IntMul xn (IntMul yd zd)
  let B' := IntMul (IntMul yn zd) xd
  let C' := IntMul (IntMul zn yd) xd
  have expandLeft :
      IntEq
        (IntAdd
          (IntMul (IntAdd (IntMul xn yd) (IntMul yn xd)) zd)
          (IntMul zn (IntMul xd yd)))
        (IntAdd (IntAdd A B) C) := by
    exact R.add_congr
      (R.right_distrib (IntMul xn yd) (IntMul yn xd) zd)
      (R.refl C)
  have aNorm : IntEq A A' :=
    R.mul_assoc xn yd zd
  have bNorm : IntEq B B' := by
    exact R.trans (R.mul_assoc yn xd zd)
      (R.trans
        (R.mul_congr (R.refl yn) (R.mul_comm xd zd))
        (R.symm (R.mul_assoc yn zd xd)))
  have cNorm : IntEq C C' := by
    exact R.trans
      (R.mul_congr (R.refl zn) (R.mul_comm xd yd))
      (R.symm (R.mul_assoc zn yd xd))
  have regroup :
      IntEq (IntAdd (IntAdd A B) C)
        (IntAdd A' (IntAdd B' C')) := by
    exact R.trans (R.add_assoc A B C)
      (R.add_congr aNorm (R.add_congr bNorm cNorm))
  have foldRight :
      IntEq (IntAdd A' (IntAdd B' C'))
        (IntAdd
          (IntMul xn (IntMul yd zd))
          (IntMul (IntAdd (IntMul yn zd) (IntMul zn yd)) xd)) := by
    exact R.add_congr (R.refl A')
      (R.symm (R.right_distrib (IntMul yn zd) (IntMul zn yd) xd))
  exact R.trans expandLeft (R.trans regroup foldRight)

private theorem ratAdd_assoc_local (x y z : BRat) :
    RatEq (ratAdd (ratAdd x y) z) (ratAdd x (ratAdd y z)) := by
  apply ratEq_of_num_den_intEq
  · have leftToStructured :
        IntEq (ratAdd (ratAdd x y) z).num
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (IntMul (ratDenInt x) (ratDenInt y)))) := by
      unfold ratAdd
      change
        IntEq
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (ratDenInt (ratAdd x y))))
          (IntAdd
            (IntMul
              (IntAdd (IntMul x.num (ratDenInt y))
                (IntMul y.num (ratDenInt x)))
              (ratDenInt z))
            (IntMul z.num (IntMul (ratDenInt x) (ratDenInt y))))
      exact IntAdd_respects (IntEq_refl _)
        (IntMul_respects (IntEq_refl z.num) (ratDenInt_add x y))
    have rightToStructured :
        IntEq (ratAdd x (ratAdd y z)).num
          (IntAdd
            (IntMul x.num (IntMul (ratDenInt y) (ratDenInt z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x))) := by
      unfold ratAdd
      change
        IntEq
          (IntAdd
            (IntMul x.num (ratDenInt (ratAdd y z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x)))
          (IntAdd
            (IntMul x.num (IntMul (ratDenInt y) (ratDenInt z)))
            (IntMul
              (IntAdd (IntMul y.num (ratDenInt z))
                (IntMul z.num (ratDenInt y)))
              (ratDenInt x)))
      exact IntAdd_respects
        (IntMul_respects (IntEq_refl x.num) (ratDenInt_add y z))
        (IntEq_refl _)
    exact IntEq_trans leftToStructured
      (IntEq_trans
        (intRatAddAssocNum_local x.num (ratDenInt x) y.num (ratDenInt y)
          z.num (ratDenInt z))
        (IntEq_symm rightToStructured))
  · have leftDen :
        IntEq (ratDenInt (ratAdd (ratAdd x y) z))
          (IntMul (IntMul (ratDenInt x) (ratDenInt y)) (ratDenInt z)) := by
      exact IntEq_trans (ratDenInt_add (ratAdd x y) z)
        (IntMul_respects (ratDenInt_add x y) (IntEq_refl (ratDenInt z)))
    have rightDen :
        IntEq (ratDenInt (ratAdd x (ratAdd y z)))
          (IntMul (ratDenInt x) (IntMul (ratDenInt y) (ratDenInt z))) := by
      exact IntEq_trans (ratDenInt_add x (ratAdd y z))
        (IntMul_respects (IntEq_refl (ratDenInt x)) (ratDenInt_add y z))
    exact IntEq_trans leftDen
      (IntEq_trans (IntMul_assoc (ratDenInt x) (ratDenInt y) (ratDenInt z))
        (IntEq_symm rightDen))

private theorem ratAdd_neg_local (x : BRat) :
    RatEq (ratAdd x (ratNeg x)) ratZero := by
  apply ratEq_zero_of_num_zero_local
  unfold ratAdd ratNeg
  change
    IntEq
      (IntAdd (IntMul x.num (ratDenInt (ratNeg x)))
        (IntMul (IntNeg x.num) (ratDenInt x))) intZero
  have leftDen :
      IntEq (IntMul x.num (ratDenInt (ratNeg x)))
        (IntMul x.num (ratDenInt x)) :=
    IntMul_respects (IntEq_refl x.num) (ratDenInt_neg_local x)
  have rightNeg :
      IntEq (IntMul (IntNeg x.num) (ratDenInt x))
        (IntNeg (IntMul x.num (ratDenInt x))) :=
    BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt x)
  exact IntEq_trans (IntAdd_respects leftDen rightNeg)
    (IntAdd_neg (IntMul x.num (ratDenInt x)))

private theorem ratNeg_neg_local (x : BRat) :
    RatEq (ratNeg (ratNeg x)) x := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_neg x.num
  · unfold ratNeg ratDenInt
    exact IntEq_refl (intOfNat x.den (ratDenCarrier (ratNeg (ratNeg x))))

private theorem ratNeg_add_dist_local (x y : BRat) :
    RatEq (ratNeg (ratAdd x y)) (ratAdd (ratNeg x) (ratNeg y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratAdd
    change
      IntEq
        (IntNeg
          (IntAdd (IntMul x.num (ratDenInt y))
            (IntMul y.num (ratDenInt x))))
        (IntAdd
          (IntMul (IntNeg x.num) (ratDenInt (ratNeg y)))
          (IntMul (IntNeg y.num) (ratDenInt (ratNeg x))))
    have leftNeg :
        IntEq
          (IntNeg
            (IntAdd (IntMul x.num (ratDenInt y))
              (IntMul y.num (ratDenInt x))))
          (IntAdd
            (IntNeg (IntMul x.num (ratDenInt y)))
            (IntNeg (IntMul y.num (ratDenInt x)))) :=
      intNeg_add_local (IntMul x.num (ratDenInt y))
        (IntMul y.num (ratDenInt x))
    have first :
        IntEq (IntNeg (IntMul x.num (ratDenInt y)))
          (IntMul (IntNeg x.num) (ratDenInt (ratNeg y))) := by
      exact IntEq_trans
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul x.num (ratDenInt y)))
        (IntMul_respects (IntEq_refl (IntNeg x.num))
          (IntEq_symm (ratDenInt_neg_local y)))
    have second :
        IntEq (IntNeg (IntMul y.num (ratDenInt x)))
          (IntMul (IntNeg y.num) (ratDenInt (ratNeg x))) := by
      exact IntEq_trans
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul y.num (ratDenInt x)))
        (IntMul_respects (IntEq_refl (IntNeg y.num))
          (IntEq_symm (ratDenInt_neg_local x)))
    exact IntEq_trans leftNeg (IntAdd_respects first second)
  · unfold ratNeg
    exact IntEq_trans (ratDenInt_neg_local (ratAdd x y))
      (IntEq_trans (ratDenInt_add x y)
        (IntEq_trans
          (IntMul_respects (IntEq_symm (ratDenInt_neg_local x))
            (IntEq_symm (ratDenInt_neg_local y)))
          (IntEq_symm (ratDenInt_add (ratNeg x) (ratNeg y)))))

private theorem ratSub_add_sub_left_cancel_local (x x' y : BRat) :
    RatEq (ratSub (ratAdd x' y) (ratSub x' x)) (ratAdd x y) := by
  unfold ratSub
  have negExpand :
      RatEq
        (ratAdd (ratAdd x' y) (ratNeg (ratAdd x' (ratNeg x))))
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') (ratNeg (ratNeg x)))) :=
    ratAdd_respects (RatEq_refl _) (ratNeg_add_dist_local x' (ratNeg x))
  have negNeg :
      RatEq
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') (ratNeg (ratNeg x))))
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') x)) :=
    ratAdd_respects (RatEq_refl _)
      (ratAdd_respects (RatEq_refl _) (ratNeg_neg_local x))
  have paired :
      RatEq
        (ratAdd (ratAdd x' y) (ratAdd (ratNeg x') x))
        (ratAdd (ratAdd x' (ratNeg x')) (ratAdd y x)) := by
    exact RatEq_trans _ _ _
      (ratAdd_assoc_local x' y (ratAdd (ratNeg x') x))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x')
          (RatEq_symm (ratAdd_assoc_local y (ratNeg x') x)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x')
            (ratAdd_respects (ratAdd_comm y (ratNeg x')) (RatEq_refl x)))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl x')
              (ratAdd_assoc_local (ratNeg x') y x))
            (RatEq_symm (ratAdd_assoc_local x' (ratNeg x') (ratAdd y x))))))
  exact RatEq_trans _ _ _ negExpand
    (RatEq_trans _ _ _ negNeg
      (RatEq_trans _ _ _ paired
        (RatEq_trans _ _ _
          (ratAdd_respects (ratAdd_neg_local x') (RatEq_refl (ratAdd y x)))
          (RatEq_trans _ _ _
            (ratZero_add_left (ratAdd y x))
            (ratAdd_comm y x)))))

private theorem ratLe_add_right_mono {x x' y : BRat} :
    ratLe x x' -> ratLe (ratAdd x y) (ratAdd x' y) := by
  intro h
  have diffNonneg : ratLe ratZero (ratSub x' x) :=
    ratSub_nonneg_of_le h
  have base :
      ratLe (ratSub (ratAdd x' y) (ratSub x' x)) (ratAdd x' y) :=
    ratSub_le_left_of_nonneg diffNonneg
  exact ratLe_respects
    (ratSub_add_sub_left_cancel_local x x' y)
    (RatEq_refl _)
    base

private theorem ratLe_add_left_mono {y y' x : BRat} :
    ratLe y y' -> ratLe (ratAdd x y) (ratAdd x y') := by
  intro h
  exact ratLe_respects
    (ratAdd_comm y x)
    (ratAdd_comm y' x)
    (ratLe_add_right_mono (x := y) (x' := y') (y := x) h)

private theorem ratLe_add_mono {x x' y y' : BRat} :
    ratLe x x' -> ratLe y y' ->
      ratLe (ratAdd x y) (ratAdd x' y') := by
  intro hx hy
  exact ratLe_trans
    (ratLe_add_right_mono (x := x) (x' := x') (y := y) hx)
    (ratLe_add_left_mono (y := y) (y' := y') (x := x') hy)

def overshootBoundsFrom
    (lambdaLo lambdaHi : BRat)
    (signedLobeLo signedLobeHi : Nat -> BRat) : Nat -> BRat × BRat
  | 0 => (lambdaLo, lambdaHi)
  | Nat.succ i =>
      let prev := overshootBoundsFrom lambdaLo lambdaHi signedLobeLo signedLobeHi i
      (ratSub (signedLobeLo i) prev.2,
        ratSub (signedLobeHi i) prev.1)

def overshootLoFrom
    (lambdaLo lambdaHi : BRat)
    (signedLobeLo signedLobeHi : Nat -> BRat) (i : Nat) : BRat :=
  (overshootBoundsFrom lambdaLo lambdaHi signedLobeLo signedLobeHi i).1

def overshootHiFrom
    (lambdaLo lambdaHi : BRat)
    (signedLobeLo signedLobeHi : Nat -> BRat) (i : Nat) : BRat :=
  (overshootBoundsFrom lambdaLo lambdaHi signedLobeLo signedLobeHi i).2

def ratNegOne : BRat :=
  ratNeg ratOne

def ratTwoCanon : BRat :=
  { num := intOfNat (BHist.e1 NatOne)
      (unary_e1_closed (unary_e1_closed unary_empty))
    den := NatOne
    den_pos := Or.inr (hsame_refl NatOne) }

def ratHalfCanon : BRat :=
  { num := intOne
    den := BHist.e1 NatOne
    den_pos :=
      Or.inl
        ⟨NatOne, unary_e1_closed unary_empty,
          BEDC.FKernel.Hist.not_hsame_e1_empty, rfl⟩ }

structure GAGCert where
  D : Nat
  rootLo : Nat -> BRat
  rootHi : Nat -> BRat
  lambdaLo : BRat
  lambdaHi : BRat
  signedLobeLo : Nat -> BRat
  signedLobeHi : Nat -> BRat

namespace GAGCert

def overshootLo (cert : GAGCert) : Nat -> BRat
  | i =>
      overshootLoFrom cert.lambdaLo cert.lambdaHi
        cert.signedLobeLo cert.signedLobeHi i

def overshootHi (cert : GAGCert) : Nat -> BRat
  | i =>
      overshootHiFrom cert.lambdaLo cert.lambdaHi
        cert.signedLobeLo cert.signedLobeHi i

def trueOvershoot (lambda : BRat) (signedLobe : Nat -> BRat) : Nat -> BRat
  | 0 => lambda
  | Nat.succ i => ratSub (signedLobe i) (trueOvershoot lambda signedLobe i)

def passes (cert : GAGCert) : Prop :=
  ratLt ratZero cert.lambdaLo ∧
    ∀ i : Nat, i < cert.D -> ratLt ratZero (cert.overshootLo (i + 1))

def ValueAbove (value lambda : BRat) : Prop :=
  ratLt lambda value

def ValueBelow (value lambda : BRat) : Prop :=
  ratLt value lambda

inductive GAGParity : Nat -> Type where
  | oddStep (k : Nat) : GAGParity (2 * k + 1)
  | evenStep (k : Nat) : GAGParity (2 * (k + 1))

def SignedLobeRelation (lambda m value : BRat) (parity : GAGParity i) : Prop :=
  match parity with
  | GAGParity.oddStep _ => RatEq value (ratAdd lambda m)
  | GAGParity.evenStep _ => RatEq lambda (ratAdd value m)

def AlternatesAcross (lambda _m value : BRat) (parity : GAGParity i) : Prop :=
  match parity with
  | GAGParity.oddStep _ => ValueAbove value lambda
  | GAGParity.evenStep _ => ValueBelow value lambda

def RootIntervalsSeparatedNegative (cert : GAGCert) : Prop :=
  (∀ i : Nat, i < cert.D -> ratLe (cert.rootLo i) (cert.rootHi i)) ∧
    (∀ i : Nat, i + 1 < cert.D -> ratLt (cert.rootHi i) (cert.rootLo (i + 1))) ∧
      (∀ i : Nat, i < cert.D -> ratLt (cert.rootHi i) ratZero)

inductive GAGRootCountObligationKind where
  | monotoneCrossingIVT
  | locatedRootExistence
  | endpointSignCrossing

-- The finite rational alternation certificate is proved here. Turning it into
-- located negative roots of I_{D+1} is a constructive located-IVT bridge over
-- the located-real layer, recorded only as obligation targets in this file.
structure GAGRootCountObligation (cert : GAGCert) where
  target : GAGRootCountObligationKind -> Prop
  rootIntervals : RootIntervalsSeparatedNegative cert

structure GAGLocatedRootCountConclusion (cert : GAGCert) where
  locatedNegativeRootCount : Nat
  count_matches_step : locatedNegativeRootCount = cert.D + 1

private theorem ratLt_le_trans_local {x y z : BRat} :
    ratLt x y -> ratLe y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) yz
  · intro zx
    exact ratLt_not_ratLe_reverse xy (ratLe_trans yz zx)

private theorem ratLt_respects_local {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratAdd_right_neg_cancel_local (x y : BRat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratLe_add_right_cancel_local {x x' y : BRat} :
    ratLe (ratAdd x y) (ratAdd x' y) -> ratLe x x' := by
  intro h
  have shifted :
      ratLe (ratAdd (ratAdd x y) (ratNeg y))
        (ratAdd (ratAdd x' y) (ratNeg y)) :=
    ratLe_add_right_mono (x := ratAdd x y) (x' := ratAdd x' y)
      (y := ratNeg y) h
  exact ratLe_respects
    (ratAdd_right_neg_cancel_local x y)
    (ratAdd_right_neg_cancel_local x' y)
    shifted

private theorem ratLt_add_right_mono_local {x x' y : BRat} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_add_right_mono (x := x) (x' := x') (y := y)
      (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_add_right_cancel_local reverse)

private theorem ratLt_add_pos_right (x y : BRat) :
    ratLt ratZero y -> ratLt x (ratAdd x y) := by
  intro hy
  have raw : ratLt (ratAdd ratZero x) (ratAdd y x) :=
    ratLt_add_right_mono_local (x := ratZero) (x' := y) (y := x) hy
  exact ratLt_respects_local (ratZero_add_left x) (ratAdd_comm y x) raw

private theorem ratLe_neg_anti_local {a b : BRat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    ratLe_add_right_mono (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm (ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects (ratAdd_neg_local a) (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm (ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects (ratAdd_neg_local b) (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratSub_le_sub_local {a b c d : BRat} :
    ratLe a b -> ratLe d c -> ratLe (ratSub a c) (ratSub b d) := by
  intro hab hdc
  unfold ratSub
  exact ratLe_add_mono hab (ratLe_neg_anti_local hdc)

theorem gag_true_overshoot_in_interval
    (cert : GAGCert)
    (lambda : BRat)
    (signedLobe : Nat -> BRat)
    (hlambda :
      ratLe cert.lambdaLo lambda ∧ ratLe lambda cert.lambdaHi)
    (hsigned :
      ∀ i : Nat,
        ratLe (cert.signedLobeLo i) (signedLobe i) ∧
          ratLe (signedLobe i) (cert.signedLobeHi i)) :
    ∀ i : Nat,
      ratLe (cert.overshootLo i)
        (trueOvershoot lambda signedLobe i) ∧
        ratLe (trueOvershoot lambda signedLobe i)
          (cert.overshootHi i) := by
  intro i
  induction i with
  | zero =>
      exact hlambda
  | succ i ih =>
      unfold trueOvershoot overshootLo overshootHi
      unfold overshootLoFrom overshootHiFrom overshootBoundsFrom
      exact
        ⟨ratSub_le_sub_local (hsigned i).left
            ih.right,
          ratSub_le_sub_local (hsigned i).right
            ih.left⟩

theorem gag_true_overshoot_pos
    (cert : GAGCert)
    (lambda : BRat)
    (signedLobe : Nat -> BRat)
    (hpass : cert.passes)
    (hin :
      ∀ i : Nat,
        ratLe (cert.overshootLo i)
          (trueOvershoot lambda signedLobe i) ∧
          ratLe (trueOvershoot lambda signedLobe i)
            (cert.overshootHi i)) :
    ∀ i : Nat, i ≤ cert.D ->
      ratLt ratZero (trueOvershoot lambda signedLobe i) := by
  intro i hi
  cases i with
  | zero =>
      exact ratLt_le_trans_local hpass.left (hin 0).left
  | succ i =>
      have stepInRange : i < cert.D :=
        Nat.lt_of_succ_le hi
      exact ratLt_le_trans_local (hpass.right i stepInRange) (hin (i + 1)).left

theorem gag_signed_lobe_alternation
    {lambda m value : BRat} {i : Nat}
    (parity : GAGParity i)
    (hm : ratLt ratZero m)
    (relation : SignedLobeRelation lambda m value parity) :
    AlternatesAcross lambda m value parity := by
  cases parity with
  | oddStep k =>
      have raw : ratLt lambda (ratAdd lambda m) :=
        ratLt_add_pos_right lambda m hm
      exact ratLt_respects_local (RatEq_refl lambda) (RatEq_symm relation) raw
  | evenStep k =>
      have raw : ratLt value (ratAdd value m) :=
        ratLt_add_pos_right value m hm
      exact ratLt_respects_local (RatEq_refl value) (RatEq_symm relation) raw

def gagCert_D1 : GAGCert :=
  { D := 1
    rootLo := fun _ => ratNegOne
    rootHi := fun _ => ratNegOne
    lambdaLo := ratHalfCanon
    lambdaHi := ratHalfCanon
    signedLobeLo := fun _ => ratOne
    signedLobeHi := fun _ => ratOne }

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLt_not_RatEq_local {x y : BRat} :
    ratLt x y -> RatEq x y -> False := by
  intro hlt same
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt at hlt
  unfold RatEq at same
  have lenEq := IntPairClassifier_length_eq same
  unfold IntMul ratDenInt at hlt
  rw [lenEq] at hlt
  exact Nat.lt_irrefl _ hlt

private theorem ratLtBool_true_to_ratLt_local {x y : BRat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  have leXY : ratLe x y := by
    unfold ratLtBool at h
    unfold ratLe BEDC.Derived.RationalUp.intLe
    apply BEDC.Derived.IntUp.pairLe_of_length_order
    · exact intToPair_carrier _
    · exact intToPair_carrier _
    · exact Nat.le_of_succ_le
        (natLeBool_true_to_le_local h)
  have notYX : ratLe y x -> False := by
    intro yx
    have xyEq : RatEq x y := ratLe_antisymm leXY yx
    exact ratLt_not_RatEq_local
      (x := x) (y := y)
      (by
        unfold ratLt intLtUp BEDC.Derived.IntUp.intLt
        unfold ratLtBool at h
        exact Nat.lt_of_succ_le
          (natLeBool_true_to_le_local h))
      xyEq
  exact ratLe_not_le_to_ratLt leXY notYX

private theorem ratHalfCanon_pos :
    ratLt ratZero ratHalfCanon := by
  exact ratLtBool_true_to_ratLt_local (by rfl)

private theorem ratOne_sub_halfCanon_pos :
    ratLt ratZero (ratSub ratOne ratHalfCanon) := by
  exact ratLtBool_true_to_ratLt_local (by rfl)

theorem gagCert_D1_passes : gagCert_D1.passes := by
  constructor
  · exact ratHalfCanon_pos
  · intro i hi
    cases i with
    | zero =>
        change ratLt ratZero (gagCert_D1.overshootLo (0 + 1))
        unfold gagCert_D1 overshootLo overshootLoFrom overshootBoundsFrom
        exact ratOne_sub_halfCanon_pos
    | succ i =>
      have impossible : i.succ ≤ 0 := by
        exact Nat.le_of_lt_succ hi
      exact False.elim (Nat.not_succ_le_zero i impossible)

def gag_onestep_hyperbolic_of_rootcount
    (cert : GAGCert)
    (_hpass : cert.passes)
    (bridge : GAGRootCountObligation cert)
    (rootcount : bridge.target GAGRootCountObligationKind.monotoneCrossingIVT ->
      bridge.target GAGRootCountObligationKind.locatedRootExistence ->
        bridge.target GAGRootCountObligationKind.endpointSignCrossing ->
          GAGLocatedRootCountConclusion cert)
    (hmonotone : bridge.target GAGRootCountObligationKind.monotoneCrossingIVT)
    (hlocated : bridge.target GAGRootCountObligationKind.locatedRootExistence)
    (hendpoint : bridge.target GAGRootCountObligationKind.endpointSignCrossing) :
    GAGLocatedRootCountConclusion cert :=
  rootcount hmonotone hlocated hendpoint

end GAGCert

end BEDC.Derived.RHRoute.GAGCertificate
