import BEDC.Derived.RationalUp

namespace BEDC.Derived.RHRoute.ZetaBoxEvaluator

open BEDC.FKernel.Mark
open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

def ratSub (x y : Rat) : Rat :=
  ratAdd x (ratNeg y)

structure RatComplex where
  re : Rat
  im : Rat

def ratComplexZero : RatComplex :=
  { re := ratZero, im := ratZero }

def ratComplexOne : RatComplex :=
  { re := ratOne, im := ratZero }

def ratComplexAdd (z w : RatComplex) : RatComplex :=
  { re := ratAdd z.re w.re, im := ratAdd z.im w.im }

def ratComplexNeg (z : RatComplex) : RatComplex :=
  { re := ratNeg z.re, im := ratNeg z.im }

def ratComplexSub (z w : RatComplex) : RatComplex :=
  ratComplexAdd z (ratComplexNeg w)

def ratComplexMul (z w : RatComplex) : RatComplex :=
  { re := ratSub (ratMul z.re w.re) (ratMul z.im w.im)
    im := ratAdd (ratMul z.re w.im) (ratMul z.im w.re) }

def ratComplexConj (z : RatComplex) : RatComplex :=
  { re := z.re, im := ratNeg z.im }

def ratComplexScale (a : Rat) (z : RatComplex) : RatComplex :=
  { re := ratMul a z.re, im := ratMul a z.im }

def ratComplexNormSq (z : RatComplex) : Rat :=
  ratAdd (ratMul z.re z.re) (ratMul z.im z.im)

def ratComplexInvApart (z : RatComplex)
    (hz : ratApart0 (ratComplexNormSq z)) : RatComplex :=
  ratComplexScale (ratInvApart (ratComplexNormSq z) hz) (ratComplexConj z)

def ratComplexDivApart (z w : RatComplex)
    (hw : ratApart0 (ratComplexNormSq w)) : RatComplex :=
  ratComplexMul z (ratComplexInvApart w hw)

def ratComplexListSum : List RatComplex -> RatComplex
  | [] => ratComplexZero
  | z :: zs => ratComplexAdd z (ratComplexListSum zs)

def ratComplexListSumMap (f : Nat -> RatComplex) : Nat -> RatComplex
  | 0 => ratComplexZero
  | Nat.succ n => ratComplexAdd (ratComplexListSumMap f n) (f n)

def RatStrictPositive (q : Rat) : Prop :=
  q.num.sign = BMark.b0 ∧ ratApart0 q

structure DyadicBallKit where
  close : Rat -> Rat -> Nat -> Prop
  close_refl : ∀ x : Rat, ∀ k : Nat, close x x k
  close_symm :
    ∀ {x y : Rat} {k : Nat}, close x y k -> close y x k
  close_weaken :
    ∀ {x y : Rat} {hi lo : Nat}, lo ≤ hi -> close x y hi -> close x y lo
  close_trans_loss :
    ∀ {x y z : Rat} {k : Nat},
      close x y (Nat.succ k) -> close y z (Nat.succ k) -> close x z k
  add_loss :
    ∀ {x x' y y' : Rat} {k : Nat},
      close x x' (Nat.succ k) -> close y y' (Nat.succ k) ->
        close (ratAdd x y) (ratAdd x' y') k
  neg_close :
    ∀ {x y : Rat} {k : Nat}, close x y k -> close (ratNeg x) (ratNeg y) k

def RatBall (_K : DyadicBallKit) (radius center sample : Rat) : Prop :=
  ratLe (ratDist center sample) radius

def RatClose (K : DyadicBallKit) (k : Nat) (x y : Rat) : Prop :=
  K.close x y k

def natJoin (a b : Nat) : Nat :=
  a + b

theorem natJoin_mono {a b c d : Nat} :
    a ≤ c -> b ≤ d -> natJoin a b ≤ natJoin c d := by
  intro hac hbd
  exact Nat.add_le_add hac hbd

theorem natJoin_left (a b : Nat) : a ≤ natJoin a b := by
  exact Nat.le_add_right a b

theorem natJoin_right (a b : Nat) : b ≤ natJoin a b := by
  exact Nat.le_add_left b a

structure LRStream (K : DyadicBallKit) where
  app : Nat -> Rat
  modulus : Nat -> Nat
  modulus_mono : ∀ {i j : Nat}, i ≤ j -> modulus i ≤ modulus j
  regular :
    ∀ k n m : Nat, modulus k ≤ n -> modulus k ≤ m ->
      K.close (app n) (app m) k

def LREq (K : DyadicBallKit) (x y : LRStream K) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n m : Nat, N ≤ n -> N ≤ m ->
    K.close (x.app n) (y.app m) k

theorem LREq_refl (K : DyadicBallKit) (x : LRStream K) :
    LREq K x x := by
  intro k
  exact Exists.intro (x.modulus k)
    (by
      intro n m hn hm
      exact x.regular k n m hn hm)

theorem LREq_symm {K : DyadicBallKit} {x y : LRStream K} :
    LREq K x y -> LREq K y x := by
  intro h k
  cases h k with
  | intro N hN =>
      exact Exists.intro N
        (by
          intro n m hn hm
          exact K.close_symm (hN m n hm hn))

theorem LREq_trans {K : DyadicBallKit} {x y z : LRStream K} :
    LREq K x y -> LREq K y z -> LREq K x z := by
  intro hxy hyz k
  cases hxy (Nat.succ k) with
  | intro Nxy hNxy =>
      cases hyz (Nat.succ k) with
      | intro Nyz hNyz =>
          let N := natJoin Nxy Nyz
          exact Exists.intro N
            (by
              intro n m hn hm
              have hxyLeft : Nxy ≤ n :=
                Nat.le_trans (natJoin_left Nxy Nyz) hn
              have hxyRight : Nxy ≤ N :=
                natJoin_left Nxy Nyz
              have hyzLeft : Nyz ≤ N :=
                natJoin_right Nxy Nyz
              have hyzRight : Nyz ≤ m :=
                Nat.le_trans (natJoin_right Nxy Nyz) hm
              have left :
                  K.close (x.app n) (y.app N) (Nat.succ k) :=
                hNxy n N hxyLeft hxyRight
              have right :
                  K.close (y.app N) (z.app m) (Nat.succ k) :=
                hNyz N m hyzLeft hyzRight
              exact K.close_trans_loss left right)

def lrOfRatCauchy (K : DyadicBallKit)
    (a : Nat -> Rat) (M : Nat -> Nat)
    (M_mono : ∀ {i j : Nat}, i ≤ j -> M i ≤ M j)
    (hc :
      ∀ k n m : Nat, M k ≤ n -> M k ≤ m ->
        K.close (a n) (a m) k) : LRStream K :=
  { app := a
    modulus := M
    modulus_mono := M_mono
    regular := hc }

def lrConst (K : DyadicBallKit) (q : Rat) : LRStream K :=
  { app := fun _ => q
    modulus := fun _ => 0
    modulus_mono := by
      intro i j hij
      exact Nat.le_refl 0
    regular := by
      intro k n m hn hm
      exact K.close_refl q k }

def lrNeg {K : DyadicBallKit} (x : LRStream K) : LRStream K :=
  { app := fun n => ratNeg (x.app n)
    modulus := x.modulus
    modulus_mono := x.modulus_mono
    regular := by
      intro k n m hn hm
      exact K.neg_close (x.regular k n m hn hm) }

def lrAdd {K : DyadicBallKit} (x y : LRStream K) : LRStream K :=
  { app := fun n => ratAdd (x.app n) (y.app n)
    modulus := fun k => natJoin (x.modulus (Nat.succ k)) (y.modulus (Nat.succ k))
    modulus_mono := by
      intro i j hij
      exact natJoin_mono
        (x.modulus_mono (Nat.succ_le_succ hij))
        (y.modulus_mono (Nat.succ_le_succ hij))
    regular := by
      intro k n m hn hm
      have hxLeft : x.modulus (Nat.succ k) ≤ n :=
        Nat.le_trans (natJoin_left (x.modulus (Nat.succ k))
          (y.modulus (Nat.succ k))) hn
      have hxRight : x.modulus (Nat.succ k) ≤ m :=
        Nat.le_trans (natJoin_left (x.modulus (Nat.succ k))
          (y.modulus (Nat.succ k))) hm
      have hyLeft : y.modulus (Nat.succ k) ≤ n :=
        Nat.le_trans (natJoin_right (x.modulus (Nat.succ k))
          (y.modulus (Nat.succ k))) hn
      have hyRight : y.modulus (Nat.succ k) ≤ m :=
        Nat.le_trans (natJoin_right (x.modulus (Nat.succ k))
          (y.modulus (Nat.succ k))) hm
      exact K.add_loss
        (x.regular (Nat.succ k) n m hxLeft hxRight)
        (y.regular (Nat.succ k) n m hyLeft hyRight) }

theorem lrAdd_respects {K : DyadicBallKit}
    {x x' y y' : LRStream K} :
    LREq K x x' -> LREq K y y' ->
      LREq K (lrAdd x y) (lrAdd x' y') := by
  intro hx hy k
  cases hx (Nat.succ k) with
  | intro Nx hNx =>
      cases hy (Nat.succ k) with
      | intro Ny hNy =>
          let N := natJoin Nx Ny
          exact Exists.intro N
            (by
              intro n m hn hm
              have hxLeft : Nx ≤ n :=
                Nat.le_trans (natJoin_left Nx Ny) hn
              have hxRight : Nx ≤ m :=
                Nat.le_trans (natJoin_left Nx Ny) hm
              have hyLeft : Ny ≤ n :=
                Nat.le_trans (natJoin_right Nx Ny) hn
              have hyRight : Ny ≤ m :=
                Nat.le_trans (natJoin_right Nx Ny) hm
              exact K.add_loss
                (hNx n m hxLeft hxRight)
                (hNy n m hyLeft hyRight))

theorem lrNeg_respects {K : DyadicBallKit}
    {x y : LRStream K} :
    LREq K x y -> LREq K (lrNeg x) (lrNeg y) := by
  intro h k
  cases h k with
  | intro N hN =>
      exact Exists.intro N
        (by
          intro n m hn hm
          exact K.neg_close (hN n m hn hm))

structure LRMulCertificate {K : DyadicBallKit}
    (x y : LRStream K) where
  work : Nat -> Nat
  work_mono : ∀ {i j : Nat}, i ≤ j -> work i ≤ work j
  sound :
    ∀ k n m : Nat,
      K.close (x.app n) (x.app m) (work k) ->
      K.close (y.app n) (y.app m) (work k) ->
        K.close (ratMul (x.app n) (y.app n))
          (ratMul (x.app m) (y.app m)) k

def lrMul {K : DyadicBallKit} (x y : LRStream K)
    (cert : LRMulCertificate x y) : LRStream K :=
  { app := fun n => ratMul (x.app n) (y.app n)
    modulus := fun k => natJoin (x.modulus (cert.work k)) (y.modulus (cert.work k))
    modulus_mono := by
      intro i j hij
      exact natJoin_mono
        (x.modulus_mono (cert.work_mono hij))
        (y.modulus_mono (cert.work_mono hij))
    regular := by
      intro k n m hn hm
      have hxLeft : x.modulus (cert.work k) ≤ n :=
        Nat.le_trans (natJoin_left (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hn
      have hxRight : x.modulus (cert.work k) ≤ m :=
        Nat.le_trans (natJoin_left (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hm
      have hyLeft : y.modulus (cert.work k) ≤ n :=
        Nat.le_trans (natJoin_right (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hn
      have hyRight : y.modulus (cert.work k) ≤ m :=
        Nat.le_trans (natJoin_right (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hm
      exact cert.sound k n m
        (x.regular (cert.work k) n m hxLeft hxRight)
        (y.regular (cert.work k) n m hyLeft hyRight) }

structure LRAwayZero {K : DyadicBallKit} (x : LRStream K) where
  sep : ∀ n : Nat, ratApart0 (x.app n)

structure LRInvCertificate {K : DyadicBallKit}
    (x : LRStream K) (away : LRAwayZero x) where
  work : Nat -> Nat
  work_mono : ∀ {i j : Nat}, i ≤ j -> work i ≤ work j
  sound :
    ∀ k n m : Nat,
      K.close (x.app n) (x.app m) (work k) ->
        K.close (ratInvApart (x.app n) (away.sep n))
          (ratInvApart (x.app m) (away.sep m)) k

def lrInv {K : DyadicBallKit} (x : LRStream K)
    (away : LRAwayZero x) (cert : LRInvCertificate x away) : LRStream K :=
  { app := fun n => ratInvApart (x.app n) (away.sep n)
    modulus := fun k => x.modulus (cert.work k)
    modulus_mono := by
      intro i j hij
      exact x.modulus_mono (cert.work_mono hij)
    regular := by
      intro k n m hn hm
      exact cert.sound k n m (x.regular (cert.work k) n m hn hm) }

structure LRTower (K : DyadicBallKit) (u : Nat -> LRStream K) where
  outer : Nat -> Nat
  inner : Nat -> Nat
  outer_mono : ∀ {i j : Nat}, i ≤ j -> outer i ≤ outer j
  inner_mono : ∀ {i j : Nat}, i ≤ j -> inner i ≤ inner j
  cauchy :
    ∀ k i j p q : Nat,
      outer k ≤ i -> outer k ≤ j ->
      inner k ≤ p -> inner k ≤ q ->
        K.close ((u i).app p) ((u j).app q) k

def lrLimit {K : DyadicBallKit} (u : Nat -> LRStream K)
    (tower : LRTower K u) : LRStream K :=
  { app := fun k => (u (tower.outer k)).app (tower.inner k)
    modulus := fun k => k
    modulus_mono := by
      intro i j hij
      exact hij
    regular := by
      intro k n m hn hm
      exact tower.cauchy k (tower.outer n) (tower.outer m)
        (tower.inner n) (tower.inner m)
        (tower.outer_mono hn) (tower.outer_mono hm)
        (tower.inner_mono hn) (tower.inner_mono hm) }

structure QInterval where
  lo : Rat
  hi : Rat
  valid : ratLe lo hi

structure ComplexBox where
  re : QInterval
  im : QInterval

structure BoxGauge where
  fits : ComplexBox -> Nat -> Prop
  fits_weaken :
    ∀ {box : ComplexBox} {hi lo : Nat}, lo ≤ hi -> fits box hi -> fits box lo

structure BoxStream (G : BoxGauge) where
  box : Nat -> ComplexBox
  modulus : Nat -> Nat
  modulus_mono : ∀ {i j : Nat}, i ≤ j -> modulus i ≤ modulus j
  fits_at :
    ∀ k n : Nat, modulus k ≤ n -> G.fits (box n) k

def boxAt {G : BoxGauge} (x : BoxStream G) (k : Nat) : ComplexBox :=
  x.box (x.modulus k)

theorem boxAt_fits {G : BoxGauge} (x : BoxStream G) (k : Nat) :
    G.fits (boxAt x k) k := by
  exact x.fits_at k (x.modulus k) (Nat.le_refl (x.modulus k))

structure ComplexBoxOpCertificate (G : BoxGauge) where
  op : ComplexBox -> ComplexBox -> ComplexBox
  work : Nat -> Nat
  work_mono : ∀ {i j : Nat}, i ≤ j -> work i ≤ work j
  sound :
    ∀ k : Nat, ∀ a b : ComplexBox,
      G.fits a (work k) -> G.fits b (work k) ->
        G.fits (op a b) k

def boxBinary {G : BoxGauge} (cert : ComplexBoxOpCertificate G)
    (x y : BoxStream G) : BoxStream G :=
  { box := fun n => cert.op (x.box n) (y.box n)
    modulus := fun k => natJoin (x.modulus (cert.work k)) (y.modulus (cert.work k))
    modulus_mono := by
      intro i j hij
      exact natJoin_mono
        (x.modulus_mono (cert.work_mono hij))
        (y.modulus_mono (cert.work_mono hij))
    fits_at := by
      intro k n hn
      have hx : x.modulus (cert.work k) ≤ n :=
        Nat.le_trans (natJoin_left (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hn
      have hy : y.modulus (cert.work k) ≤ n :=
        Nat.le_trans (natJoin_right (x.modulus (cert.work k))
          (y.modulus (cert.work k))) hn
      exact cert.sound k (x.box n) (y.box n)
        (x.fits_at (cert.work k) n hx)
        (y.fits_at (cert.work k) n hy) }

structure ComplexApproxKernel (G : BoxGauge) where
  lnNat : Nat -> BoxStream G
  smallExp : RatComplex -> BoxStream G
  rangeReducedExp : RatComplex -> BoxStream G
  negSLogNat : Nat -> BoxStream G

structure CriticalStripInput where
  re : Rat
  im : Rat
  sigmaLower : Rat
  sigmaUpperGap : Rat
  imagBound : Rat
  sigmaLower_pos : RatStrictPositive sigmaLower
  sigmaUpperGap_pos : RatStrictPositive sigmaUpperGap
  re_lower : ratLe sigmaLower re
  re_upper : ratLe re (ratSub ratOne sigmaUpperGap)

def etaPairTermBox {G : BoxGauge} (kernel : ComplexApproxKernel G)
    (pairIndex precision : Nat)
    (reValid :
      let oddIndex := Nat.succ (pairIndex + pairIndex)
      let evenIndex := Nat.succ oddIndex
      let oddBox := (kernel.negSLogNat oddIndex).box precision
      let evenBox := (kernel.negSLogNat evenIndex).box precision
      ratLe (ratSub oddBox.re.lo evenBox.re.hi)
        (ratSub oddBox.re.hi evenBox.re.lo))
    (imValid :
      let oddIndex := Nat.succ (pairIndex + pairIndex)
      let evenIndex := Nat.succ oddIndex
      let oddBox := (kernel.negSLogNat oddIndex).box precision
      let evenBox := (kernel.negSLogNat evenIndex).box precision
      ratLe (ratSub oddBox.im.lo evenBox.im.hi)
        (ratSub oddBox.im.hi evenBox.im.lo)) : ComplexBox :=
  let oddIndex := Nat.succ (pairIndex + pairIndex)
  let evenIndex := Nat.succ oddIndex
  let oddBox := (kernel.negSLogNat oddIndex).box precision
  let evenBox := (kernel.negSLogNat evenIndex).box precision
  { re :=
      { lo := ratSub oddBox.re.lo evenBox.re.hi
        hi := ratSub oddBox.re.hi evenBox.re.lo
        valid := reValid }
    im :=
      { lo := ratSub oddBox.im.lo evenBox.im.hi
        hi := ratSub oddBox.im.hi evenBox.im.lo
        valid := imValid } }

structure EtaPairTermCertificate (G : BoxGauge)
    (kernel : ComplexApproxKernel G) where
  pairTerm : Nat -> Nat -> ComplexBox
  pairTerm_source :
    ∀ pairIndex precision : Nat,
      ∃ reValid :
        (let oddIndex := Nat.succ (pairIndex + pairIndex)
         let evenIndex := Nat.succ oddIndex
         let oddBox := (kernel.negSLogNat oddIndex).box precision
         let evenBox := (kernel.negSLogNat evenIndex).box precision
         ratLe (ratSub oddBox.re.lo evenBox.re.hi)
          (ratSub oddBox.re.hi evenBox.re.lo)),
      ∃ imValid :
        (let oddIndex := Nat.succ (pairIndex + pairIndex)
         let evenIndex := Nat.succ oddIndex
         let oddBox := (kernel.negSLogNat oddIndex).box precision
         let evenBox := (kernel.negSLogNat evenIndex).box precision
         ratLe (ratSub oddBox.im.lo evenBox.im.hi)
          (ratSub oddBox.im.hi evenBox.im.lo)),
        pairTerm pairIndex precision =
          etaPairTermBox kernel pairIndex precision reValid imValid

def etaPairPartialSumBox {G : BoxGauge} {kernel : ComplexApproxKernel G}
    (addCert : ComplexBoxOpCertificate G)
    (termCert : EtaPairTermCertificate G kernel)
    (cutoff precision : Nat) : ComplexBox :=
  match cutoff with
  | 0 =>
      { re := { lo := ratZero, hi := ratZero, valid := ratLe_refl ratZero }
        im := { lo := ratZero, hi := ratZero, valid := ratLe_refl ratZero } }
  | Nat.succ n =>
      addCert.op
        (etaPairPartialSumBox addCert termCert n precision)
        (termCert.pairTerm n precision)

structure EtaPairTailCertificate (G : BoxGauge)
    (kernel : ComplexApproxKernel G)
    (addCert : ComplexBoxOpCertificate G)
    (termCert : EtaPairTermCertificate G kernel) where
  cutoff : Nat -> Nat
  workPrecision : Nat -> Nat
  cutoff_positive : ∀ k : Nat, 0 < cutoff k
  work_covers : ∀ k : Nat, k ≤ workPrecision k
  etaBox : Nat -> ComplexBox
  etaBox_eq :
    ∀ k : Nat, etaBox k =
      etaPairPartialSumBox addCert termCert (cutoff k) (workPrecision k)
  eta_fits : ∀ k : Nat, G.fits (etaBox k) k

structure DenominatorSeparation (_s : CriticalStripInput) (G : BoxGauge) where
  twoPowOneMinusS : BoxStream G
  lowerBound : Rat
  lowerBound_pos : RatStrictPositive lowerBound
  denominatorCenter : RatComplex
  denominator_apart : ratApart0 (ratComplexNormSq denominatorCenter)
  separation_fits : ∀ k : Nat, G.fits (boxAt twoPowOneMinusS k) k

structure ZetaDivisionCertificate (G : BoxGauge)
    (denominator : RatComplex)
    (denominator_apart : ratApart0 (ratComplexNormSq denominator)) where
  divide : ComplexBox -> ComplexBox
  work : Nat -> Nat
  work_mono : ∀ {i j : Nat}, i ≤ j -> work i ≤ work j
  sound :
    ∀ k : Nat, ∀ etaBox : ComplexBox,
      G.fits etaBox (work k) ->
        G.fits (divide etaBox) k
  centerDivides :
    ∀ eta : RatComplex,
      divide
        { re := { lo := eta.re, hi := eta.re, valid := ratLe_refl eta.re }
          im := { lo := eta.im, hi := eta.im, valid := ratLe_refl eta.im } } =
      { re :=
          { lo := (ratComplexDivApart eta denominator
              denominator_apart).re
            hi := (ratComplexDivApart eta denominator
              denominator_apart).re
            valid := ratLe_refl
              (ratComplexDivApart eta denominator
                denominator_apart).re }
        im :=
          { lo := (ratComplexDivApart eta denominator
              denominator_apart).im
            hi := (ratComplexDivApart eta denominator
              denominator_apart).im
            valid := ratLe_refl
              (ratComplexDivApart eta denominator
                denominator_apart).im } }

structure ZetaBoxEvaluator (G : BoxGauge) (s : CriticalStripInput) where
  kernel : ComplexApproxKernel G
  boxAdd : ComplexBoxOpCertificate G
  etaPairTerm : EtaPairTermCertificate G kernel
  etaTail : EtaPairTailCertificate G kernel boxAdd etaPairTerm
  denominator : DenominatorSeparation s G
  division :
    ZetaDivisionCertificate G denominator.denominatorCenter
      denominator.denominator_apart

def zetaBox {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) : ComplexBox :=
  E.division.divide (E.etaTail.etaBox (E.division.work k))

structure ZetaPrecisionPacket {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) where
  etaPrecision : Nat
  etaBox : ComplexBox
  eta_fits : G.fits etaBox etaPrecision
  zetaBox : ComplexBox
  zetaBox_eq : zetaBox = E.division.divide etaBox
  zeta_fits : G.fits zetaBox k
  denominator_apart :
    ratApart0 (ratComplexNormSq E.denominator.denominatorCenter)

theorem zetaBoxEvaluableToPrecision {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) :
    ∃ packet : ZetaPrecisionPacket E k, G.fits packet.zetaBox k := by
  let etaPrecision := E.division.work k
  let etaBox := E.etaTail.etaBox etaPrecision
  have etaFits : G.fits etaBox etaPrecision :=
    E.etaTail.eta_fits etaPrecision
  have zetaFits : G.fits (E.division.divide etaBox) k :=
    E.division.sound k etaBox etaFits
  exact Exists.intro
    { etaPrecision := etaPrecision
      etaBox := etaBox
      eta_fits := etaFits
      zetaBox := E.division.divide etaBox
      zetaBox_eq := rfl
      zeta_fits := zetaFits
      denominator_apart := E.denominator.denominator_apart }
    zetaFits

theorem zetaBox_fits {G : BoxGauge} {s : CriticalStripInput}
    (E : ZetaBoxEvaluator G s) (k : Nat) :
    G.fits (zetaBox E k) k := by
  exact E.division.sound k (E.etaTail.etaBox (E.division.work k))
    (E.etaTail.eta_fits (E.division.work k))

end BEDC.Derived.RHRoute.ZetaBoxEvaluator
