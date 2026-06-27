import BEDC.Derived.RHRoute.ConstructiveZeta
import BEDC.Derived.RHRoute.EtaInteger

set_option maxHeartbeats 1000000

namespace BEDC.Derived.RHRoute.EtaKernelDischarge

open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal
open BEDC.Derived.RHRoute.AltConvergence
open BEDC.Derived.RHRoute.ConstructiveZeta
open BEDC.Derived.RHRoute.AlternatingTailBound

abbrev Rat := RatNum

def ratComplexOfRat (q : Rat) : RatComplex :=
  { re := q, im := ratZero }

def locatedComplexOfRat (q : Rat) : LocatedComplex :=
  { approximate := fun _ =>
      { center := ratComplexOfRat q
        diameterExp := 0 } }

theorem locatedComplexOfRat_center (q : Rat) (precision : Nat) :
    (locatedComplexOfRat q).approximate precision =
      { center := ratComplexOfRat q, diameterExp := 0 } := by
  rfl

def locatedRealOfRat (q : Rat) : LocatedReal :=
  { approximate := fun _ =>
      { center := q
        diameterExp := 0 } }

/--
The exact integer eta kernel over any supplied rational strip point.
For the intended point `re = k, im = 0`, `ConstructiveZeta.RationalStripPoint`
also requires apartness from the zeta pole.  That field cannot hold at `k = 1`,
so this kernel is parameterized by the strip point rather than manufacturing a
false pole-apart proof.
-/
def intEtaKernel (s : RationalStripPoint) (k : Nat) :
    LocatedExpLogKernel s :=
  { logNat := fun _ => locatedRealOfRat ratZero
    expNegSLogNat := fun m => locatedComplexOfRat (etaIntTerm k (m - 1)) }

theorem intEtaKernel_term_center (s : RationalStripPoint) (k : Nat)
    (n precision : Nat) :
    (locatedNegativePower (intEtaKernel s k) (Nat.succ n) precision).center =
      ratComplexOfRat (etaIntTerm k n) := by
  rfl

theorem intEtaKernel_term_approx (s : RationalStripPoint) (k : Nat)
    (n precision : Nat) :
    etaTermApprox (intEtaKernel s k) n precision =
      etaSignedTerm n (ratComplexOfRat (etaIntTerm k n)) := by
  unfold etaTermApprox etaSignedTerm
  rw [intEtaKernel_term_center s k n precision]

def intEtaSignedTerm (k index : Nat) : RatComplex :=
  etaSignedTerm index (ratComplexOfRat (etaIntTerm k index))

def intEtaExactPartialSum (k N : Nat) : RatComplex :=
  ratComplexListSum (List.map (fun index => intEtaSignedTerm k index) (List.range N))

def intEtaRangePartialSum (k start len : Nat) : RatComplex :=
  ratComplexListSum
    (List.map (fun index => intEtaSignedTerm k index) (List.range' start len))

def signedRat (index : Nat) (q : Rat) : Rat :=
  (etaSignedTerm index (ratComplexOfRat q)).re

def signedRatListSum : List Rat -> Rat
  | [] => ratZero
  | q :: qs => ratAdd q (signedRatListSum qs)

def signedRatRangeSum (a : Nat -> Rat) (start len : Nat) : Rat :=
  signedRatListSum
    (List.map (fun index => signedRat index (a index)) (List.range' start len))

theorem signedRat_zero (q : Rat) :
    signedRat 0 q = q := by
  rfl

theorem signedRat_one (q : Rat) :
    signedRat 1 q = ratNeg q := by
  rfl

theorem altPartialSum_shift (a : Nat -> Rat) (start offset N : Nat) :
    altPartialSum (fun index => a (start + index)) offset N =
      altPartialSum a (start + offset) N := by
  induction N generalizing start offset with
  | zero =>
      rfl
  | succ N ih =>
      unfold altPartialSum
      rw [ih start (offset + 1)]
      rw [Nat.add_assoc]

theorem altPartialSum_succ_fn (a : Nat -> Rat) (offset N : Nat) :
    altPartialSum (fun index => a (index + 1)) offset N =
      altPartialSum a (offset + 1) N := by
  induction N generalizing offset with
  | zero =>
      rfl
  | succ N ih =>
      unfold altPartialSum
      rw [ih (offset + 1)]

theorem altPartialSum_succ_succ_fn (a : Nat -> Rat) (offset N : Nat) :
    altPartialSum (fun index => a ((index + 1) + 1)) offset N =
      altPartialSum a ((offset + 1) + 1) N := by
  induction N generalizing offset with
  | zero =>
      rfl
  | succ N ih =>
      unfold altPartialSum
      rw [ih (offset + 1)]

theorem range'_succ_map (start len : Nat) :
    List.range' (start + 1) len = List.map Nat.succ (List.range' start len) := by
  induction len generalizing start with
  | zero =>
      rfl
  | succ len ih =>
      rw [List.range'_succ, List.range'_succ]
      simp only [List.map_cons]
      rw [ih (start + 1)]

theorem map_succ_signed (a : Nat -> Rat) (xs : List Nat) :
    List.map (fun index => signedRat index (a index)) (List.map Nat.succ xs) =
      List.map (fun index => signedRat (Nat.succ index) (a (Nat.succ index))) xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [ih]

theorem map_succ_signed_tail (a : Nat -> Rat) (xs : List Nat) :
    List.map (fun index => signedRat (Nat.succ index) (a (Nat.succ index)))
        (List.map Nat.succ xs) =
      List.map
        (fun index => signedRat (Nat.succ (Nat.succ index))
          (a (Nat.succ (Nat.succ index)))) xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [ih]

theorem ratComplexOfRat_add (x y : Rat) :
    RatComplexEq (ratComplexOfRat (ratAdd x y))
      (ratComplexAdd (ratComplexOfRat x) (ratComplexOfRat y)) := by
  exact ⟨RatEq_refl _, RatEq_refl _⟩

theorem ratComplexOfRat_neg (x : Rat) :
    RatComplexEq (ratComplexOfRat (ratNeg x))
      (ratComplexNeg (ratComplexOfRat x)) := by
  exact ⟨RatEq_refl _, RatEq_refl _⟩

theorem ratComplexEq_symm {z w : RatComplex} :
    RatComplexEq z w -> RatComplexEq w z := by
  intro h
  exact ⟨RatEq_symm h.left, RatEq_symm h.right⟩

theorem ratComplexEq_trans {z w u : RatComplex} :
    RatComplexEq z w -> RatComplexEq w u -> RatComplexEq z u := by
  intro zw wu
  exact ⟨RatEq_trans z.re w.re u.re zw.left wu.left,
    RatEq_trans z.im w.im u.im zw.right wu.right⟩

theorem ratComplexAdd_respects {z z' w w' : RatComplex} :
    RatComplexEq z z' -> RatComplexEq w w' ->
      RatComplexEq (ratComplexAdd z w) (ratComplexAdd z' w') := by
  intro zz' ww'
  exact ⟨ratAdd_respects zz'.left ww'.left,
    ratAdd_respects zz'.right ww'.right⟩

theorem ratComplexNeg_respects {z w : RatComplex} :
    RatComplexEq z w -> RatComplexEq (ratComplexNeg z) (ratComplexNeg w) := by
  intro zw
  exact ⟨ratNeg_respects zw.left, ratNeg_respects zw.right⟩

theorem ratComplexOfRat_zero :
    RatComplexEq (ratComplexOfRat ratZero) ratComplexZero := by
  exact RatComplexEq_refl _

theorem ratNeg_zero :
    RatEq (ratNeg ratZero) ratZero := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAdd_zero_right (ratNeg ratZero)))
    (ratNeg_add ratZero)

theorem ratComplexNeg_zero :
    RatComplexEq (ratComplexNeg ratComplexZero) ratComplexZero := by
  exact ⟨ratNeg_zero, ratNeg_zero⟩

theorem ratComplexNeg_neg (z : RatComplex) :
    RatComplexEq (ratComplexNeg (ratComplexNeg z)) z := by
  exact ⟨ratNeg_neg z.re, ratNeg_neg z.im⟩

theorem ratComplexNeg_add_dist (z w : RatComplex) :
    RatComplexEq (ratComplexNeg (ratComplexAdd z w))
      (ratComplexAdd (ratComplexNeg z) (ratComplexNeg w)) := by
  exact ⟨ratNeg_add_dist z.re w.re, ratNeg_add_dist z.im w.im⟩

theorem etaSignedTerm_re_pair (a : Nat -> Rat) :
    ∀ N : Nat,
      RatEq
        (signedRatListSum
          (List.map (fun index => signedRat index (a index)) (List.range N)))
        (altPartialSum a 0 N) ∧
      RatEq
        (signedRatListSum
          (List.map
            (fun index => signedRat (Nat.succ index) (a (Nat.succ index)))
            (List.range N)))
        (ratNeg (altPartialSum (fun index => a (index + 1)) 0 N)) ∧
      True
  | 0 => by
      exact ⟨RatEq_refl _, ratNeg_zero, True.intro⟩
  | Nat.succ N => by
      rw [List.range_eq_range']
      rw [List.range'_succ]
      rw [range'_succ_map 0 N]
      simp only [List.map_cons]
      rw [map_succ_signed a (List.range' 0 N)]
      rw [map_succ_signed_tail a (List.range' 0 N)]
      rw [← List.range_eq_range']
      unfold signedRatListSum altPartialSum
      have ih := etaSignedTerm_re_pair a N
      have shifted2 := etaSignedTerm_re_pair
        (fun index => a ((index + 1) + 1)) N
      have first :
          RatEq
            (ratAdd (a 0)
              (signedRatListSum
                (List.map
                  (fun x => signedRat (Nat.succ x) (a (Nat.succ x)))
                  (List.range N))))
            (ratAdd (a 0)
              (ratNeg (altPartialSum (fun index => a (index + 1)) 0 N))) :=
        ratAdd_respects (RatEq_refl _) ih.right.left
      have secondTail :
          RatEq
            (signedRatListSum
              (List.map
                (fun x => signedRat (Nat.succ (Nat.succ x))
                  (a (Nat.succ (Nat.succ x))))
                (List.range N)))
            (altPartialSum (fun index => a ((index + 1) + 1)) 0 N) := by
        exact shifted2.left
      have second :
          RatEq
            (ratAdd (ratNeg (a (Nat.succ 0)))
              (signedRatListSum
                (List.map
                  (fun x => signedRat (Nat.succ (Nat.succ x))
                    (a (Nat.succ (Nat.succ x))))
                  (List.range N))))
            (ratNeg
              (ratAdd (a (0 + 1))
                (ratNeg (altPartialSum
                  (fun index => a ((index + 1) + 1)) 0 N)))) := by
        exact RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl _) secondTail)
          (RatEq_symm
            (RatEq_trans _ _ _
              (ratNeg_add_dist (a (0 + 1))
                (ratNeg
                  (altPartialSum (fun index => a ((index + 1) + 1)) 0 N)))
              (ratAdd_respects (RatEq_refl _)
                (ratNeg_neg _))))
      refine ⟨?_, ?_, True.intro⟩
      · simpa only [signedRat_zero, Function.comp_apply, Nat.zero_add,
          altPartialSum_succ_fn] using first
      · simpa only [signedRat_one, Function.comp_apply, Nat.zero_add,
          altPartialSum_succ_succ_fn, altPartialSum_succ_fn] using second

theorem etaSignedTerm_shift_re (a : Nat -> Rat) (N : Nat) :
    RatEq
      (signedRatListSum
        (List.map (fun index => signedRat index (a index)) (List.range N)))
      (altPartialSum a 0 N) :=
  (etaSignedTerm_re_pair a N).left

theorem etaSignedTerm_shift_im_zero (a : Nat -> Rat) (N : Nat) :
    RatEq
      (ratComplexListSum
        (List.map
          (fun index => etaSignedTerm index (ratComplexOfRat (a index)))
          (List.range N))).im
      ratZero := by
  induction List.range N with
  | nil =>
      exact RatEq_refl _
  | cons index rest ih =>
      simp only [List.map_cons]
      unfold ratComplexListSum
      have headZero :
          RatEq (etaSignedTerm index (ratComplexOfRat (a index))).im ratZero := by
        unfold etaSignedTerm ratComplexOfRat ratComplexNeg
        cases etaSignPositive index
        · exact RatEq_refl _
        · exact ratNeg_zero
      exact RatEq_trans _ _ _
        (ratAdd_respects headZero ih)
        (ratZero_add_left ratZero)

theorem signedRatListSum_eq_complex_re (a : Nat -> Rat) (N : Nat) :
    (ratComplexListSum
      (List.map
        (fun index => etaSignedTerm index (ratComplexOfRat (a index)))
        (List.range N))).re =
      signedRatListSum
        (List.map (fun index => signedRat index (a index)) (List.range N)) := by
  induction List.range N with
  | nil =>
      rfl
  | cons index rest ih =>
      simp only [List.map_cons]
      unfold ratComplexListSum signedRatListSum
      change
        ratAdd (etaSignedTerm index (ratComplexOfRat (a index))).re
          (ratComplexListSum
            (List.map
              (fun index => etaSignedTerm index (ratComplexOfRat (a index)))
              rest)).re =
        ratAdd (etaSignedTerm index (ratComplexOfRat (a index))).re
          (signedRatListSum
              (List.map
              (fun index => signedRat index (a index))
              rest))
      rw [ih]

theorem etaSignedTerm_shift (a : Nat -> Rat) (N : Nat) :
    RatComplexEq
      (ratComplexListSum
        (List.map
          (fun index => etaSignedTerm index (ratComplexOfRat (a index)))
          (List.range N)))
      (ratComplexOfRat (altPartialSum a 0 N)) := by
  constructor
  · rw [signedRatListSum_eq_complex_re a N]
    exact etaSignedTerm_shift_re a N
  · exact etaSignedTerm_shift_im_zero a N

theorem intEtaExactPartialSum_alt (k N : Nat) :
    RatComplexEq (intEtaExactPartialSum k N)
      (ratComplexOfRat (altPartialSum (etaIntTerm k) 0 N)) := by
  unfold intEtaExactPartialSum intEtaSignedTerm
  exact etaSignedTerm_shift (etaIntTerm k) N

theorem intEtaKernel_partialSum_exact (s : RationalStripPoint) (k : Nat)
    (N precision : Nat) :
    etaPartialSum (intEtaKernel s k) N precision =
      intEtaExactPartialSum k N := by
  unfold etaPartialSum etaTermList intEtaExactPartialSum intEtaSignedTerm
  induction List.range N with
  | nil =>
      rfl
  | cons index rest ih =>
      simp only [List.map_cons]
      unfold ratComplexListSum
      rw [intEtaKernel_term_approx s k index precision]
      exact congrArg (fun tail => ratComplexAdd (etaSignedTerm index
        (ratComplexOfRat (etaIntTerm k index))) tail) ih

def intEtaKernelEtaSeq (s : RationalStripPoint) (k precision : Nat) :
    Nat -> LReal (RatToleranceMetricKit groundedRatToleranceLaws) :=
  fun N => ratToLReal (RatToleranceMetricKit groundedRatToleranceLaws)
    (etaPartialSum (intEtaKernel s k) N precision).re

theorem intEtaKernel_etaPartialSum_re_eq_alt
    (s : RationalStripPoint) (k N precision : Nat) :
    RatEq (etaPartialSum (intEtaKernel s k) N precision).re
      (altPartialSum (etaIntTerm k) 0 N) := by
  rw [intEtaKernel_partialSum_exact s k N precision]
  exact (intEtaExactPartialSum_alt k N).left

theorem intEtaKernel_etaPartialSum_im_zero
    (s : RationalStripPoint) (k N precision : Nat) :
    RatEq (etaPartialSum (intEtaKernel s k) N precision).im ratZero := by
  rw [intEtaKernel_partialSum_exact s k N precision]
  exact (intEtaExactPartialSum_alt k N).right

def intEtaKernel_etaPartialSum_converges
    (s : RationalStripPoint) (k : Nat) (hk : 1 ≤ k) (precision : Nat) :
    LRealSeqCauchy (intEtaKernelEtaSeq s k precision) := by
  let base := groundedAltCauchy (etaIntLeibniz k hk)
  exact {
    index := fun j => base.index (Nat.succ (Nat.succ j))
    index_mono := by
      intro i j hij
      exact base.index_mono (Nat.succ_le_succ (Nat.succ_le_succ hij))
    cauchy := by
      intro j m n hm hn
      unfold intEtaKernelEtaSeq
      unfold ratToLReal
      change
        ratToleranceClose
          (etaPartialSum (intEtaKernel s k) m precision).re
          (etaPartialSum (intEtaKernel s k) n precision).re j
      have leftEq :
          RatEq (etaPartialSum (intEtaKernel s k) m precision).re
            (altPartialSum (etaIntTerm k) 0 m) :=
        intEtaKernel_etaPartialSum_re_eq_alt s k m precision
      have rightEq :
          RatEq (etaPartialSum (intEtaKernel s k) n precision).re
            (altPartialSum (etaIntTerm k) 0 n) :=
        intEtaKernel_etaPartialSum_re_eq_alt s k n precision
      have baseClose :
          ratToleranceClose (altPartialSum (etaIntTerm k) 0 m)
            (altPartialSum (etaIntTerm k) 0 n) (Nat.succ (Nat.succ j)) := by
        exact base.cauchy (Nat.succ (Nat.succ j)) m n hm hn
      have first :
          ratToleranceClose
            (etaPartialSum (intEtaKernel s k) m precision).re
            (altPartialSum (etaIntTerm k) 0 n) (Nat.succ j) :=
        groundedRatToleranceLaws.close_triangle
          (groundedRatToleranceLaws.eq_close leftEq (Nat.succ (Nat.succ j)))
          baseClose
      exact groundedRatToleranceLaws.close_triangle
        first
        (groundedRatToleranceLaws.eq_close (RatEq_symm rightEq) (Nat.succ j))
  }

/--
`ConstructiveZeta.EtaTailWitness` records only budget numerals and the inequality
`targetPrecision <= tailDiameterExp`; it does not mention the kernel or a
Cauchy argument.  This packet is the integer-s discharge it omits: the
ConstructiveZeta kernel has exact signed rational centers, while convergence is
the grounded Leibniz Cauchy proof and located limit supplied by `etaIntLimit`.
The missing complex case is the construction of located complex `exp(-s log n)`.
-/
structure IntEtaKernelConvergence
    (s : RationalStripPoint) (k : Nat) (hk : 1 ≤ k) where
  cauchy :
    LRealSeqCauchy (intEtaKernelEtaSeq s k 0)
  limit : LReal (RatToleranceMetricKit groundedRatToleranceLaws)
  limit_eq_etaIntLimit : limit = etaIntLimit k hk
  exact_terms :
    ∀ n precision : Nat,
      etaTermApprox (intEtaKernel s k) n precision = intEtaSignedTerm k n
  exact_partial_sums :
    ∀ N precision : Nat,
      etaPartialSum (intEtaKernel s k) N precision = intEtaExactPartialSum k N
  partial_sum_re_eq_alt :
    ∀ N precision : Nat,
      RatEq (etaPartialSum (intEtaKernel s k) N precision).re
        (altPartialSum (etaIntTerm k) 0 N)
  partial_sum_im_zero :
    ∀ N precision : Nat,
      RatEq (etaPartialSum (intEtaKernel s k) N precision).im ratZero
  modulus : Nat -> Nat
  modulus_eq :
    modulus = fun j => (etaIntLeibniz k hk).zeroIndex (Nat.succ (Nat.succ j))

def intEtaKernel_convergence
    (s : RationalStripPoint) (k : Nat) (hk : 1 ≤ k) :
    IntEtaKernelConvergence s k hk :=
  { cauchy := intEtaKernel_etaPartialSum_converges s k hk 0
    limit := etaIntLimit k hk
    limit_eq_etaIntLimit := rfl
    exact_terms := intEtaKernel_term_approx s k
    exact_partial_sums := intEtaKernel_partialSum_exact s k
    partial_sum_re_eq_alt := intEtaKernel_etaPartialSum_re_eq_alt s k
    partial_sum_im_zero := intEtaKernel_etaPartialSum_im_zero s k
    modulus := fun j => (etaIntLeibniz k hk).zeroIndex (Nat.succ (Nat.succ j))
    modulus_eq := rfl }

theorem intEtaKernel_converges
    (s : RationalStripPoint) (k : Nat) (hk : 1 ≤ k) :
    Nonempty (IntEtaKernelConvergence s k hk) :=
  ⟨intEtaKernel_convergence s k hk⟩

theorem intEtaKernel_convergence_modulus
    (s : RationalStripPoint) (k : Nat) (hk : 1 ≤ k) :
    (intEtaKernel_convergence s k hk).modulus =
      fun j => powTwoNat (Nat.succ (Nat.succ j)) := by
  rfl

end BEDC.Derived.RHRoute.EtaKernelDischarge
