import BEDC.Derived.ZModUp
import BEDC.Derived.GcdUp
import BEDC.Derived.IntUp.CommRing
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.CRTUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.IntUp
open BEDC.Derived.GcdUp
open BEDC.Derived.ZModUp
open BEDC.FKernel.ExternalBinary (bwordLength)

def crtModulus (m n : BHist) : BHist :=
  natMulFn m n

def crtProductNonempty {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False) :
    hsame (crtModulus m n) BHist.Empty -> False := by
  intro productEmpty
  exact NatMul_nonempty_factors_result_not_empty mNonempty nNonempty
    (natMulFn_rel mUnary nUnary) productEmpty

def crtForward {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : ZMod (crtModulus m n)) : ZMod m × ZMod n :=
  (zmodFromNat m mUnary mNonempty x.val
      (zmodVal_unary (natMulFn_unary mUnary nUnary) x),
    zmodFromNat n nUnary nNonempty x.val
      (zmodVal_unary (natMulFn_unary mUnary nUnary) x))

def crtBezoutCoeffs (m n : BHist) : (BHist × BHist) × (BHist × BHist) :=
  natBezoutFn m n

def crtTermLeft (m : BHist) (x : BHist × BHist) (b : BHist) : BHist × BHist :=
  pairMul (b, BHist.Empty) (pairMul x (m, BHist.Empty))

def crtTermRight (n : BHist) (y : BHist × BHist) (a : BHist) : BHist × BHist :=
  pairMul (a, BHist.Empty) (pairMul y (n, BHist.Empty))

def crtReconstructPair (m n : BHist) (a : ZMod m) (b : ZMod n) : BHist × BHist :=
  let coeffs := crtBezoutCoeffs m n
  pairAdd (crtTermLeft m coeffs.1 b.val) (crtTermRight n coeffs.2 a.val)

theorem crtTermLeft_carrier {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (b : ZMod n) :
    IntPairCarrier
      (crtTermLeft m (crtBezoutCoeffs m n).1 b.val).1
      (crtTermLeft m (crtBezoutCoeffs m n).1 b.val).2 := by
  have coeffCarrier := natBezoutFn_carrier mUnary nUnary
  exact pairMul_carrier
    ⟨zmodVal_unary nUnary b, unary_empty⟩
    (pairMul_carrier coeffCarrier.left ⟨mUnary, unary_empty⟩)

theorem crtTermRight_carrier {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (a : ZMod m) :
    IntPairCarrier
      (crtTermRight n (crtBezoutCoeffs m n).2 a.val).1
      (crtTermRight n (crtBezoutCoeffs m n).2 a.val).2 := by
  have coeffCarrier := natBezoutFn_carrier mUnary nUnary
  exact pairMul_carrier
    ⟨zmodVal_unary mUnary a, unary_empty⟩
    (pairMul_carrier coeffCarrier.right ⟨nUnary, unary_empty⟩)

theorem crtReconstructPair_carrier {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (a : ZMod m) (b : ZMod n) :
    IntPairCarrier (crtReconstructPair m n a b).1
      (crtReconstructPair m n a b).2 := by
  unfold crtReconstructPair
  exact pairAdd_carrier
    (crtTermLeft_carrier mUnary nUnary b)
    (crtTermRight_carrier mUnary nUnary a)

def crtPairResidue (M : BHist) (p : BHist × BHist) : BHist :=
  natModFn M (append p.1 (natComplementMod M p.2))

def crtInverse {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (pair : ZMod m × ZMod n) : ZMod (crtModulus m n) :=
  let M := crtModulus m n
  let raw := crtReconstructPair m n pair.1 pair.2
  { val := crtPairResidue M raw
    isLt :=
      natModFn_lt (natMulFn_unary mUnary nUnary)
        (unary_append_closed
          (crtReconstructPair_carrier mUnary nUnary pair.1 pair.2).left
          (natComplementMod_unary (natMulFn_unary mUnary nUnary)))
        (crtProductNonempty mUnary nUnary mNonempty nNonempty) }

theorem crtModulus_unary {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    UnaryHistory (crtModulus m n) :=
  natMulFn_unary mUnary nUnary

theorem crtModulus_mul_rel {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    NatMul m n (crtModulus m n) :=
  natMulFn_rel mUnary nUnary

theorem crtModulus_comm_mul_rel {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    NatMul n m (crtModulus m n) := by
  have productNM : NatMul n m (natMulFn n m) :=
    natMulFn_rel nUnary mUnary
  have sameProduct : hsame (crtModulus m n) (natMulFn n m) :=
    NatMul_comm_hsame mUnary nUnary
      (crtModulus_mul_rel mUnary nUnary) productNM
  exact (NatMul_result_hsame_transport productNM (hsame_symm sameProduct)).right

theorem crtModulus_left_divides {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    NatDivides m (crtModulus m n) :=
  ⟨n, nUnary, crtModulus_mul_rel mUnary nUnary⟩

theorem crtModulus_right_divides {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    NatDivides n (crtModulus m n) := by
  have productNM : NatMul n m (natMulFn n m) :=
    natMulFn_rel nUnary mUnary
  have sameProduct : hsame (crtModulus m n) (natMulFn n m) :=
    NatMul_comm_hsame mUnary nUnary
      (crtModulus_mul_rel mUnary nUnary) productNM
  exact (NatDivides_dividend_hsame_transport
    ⟨m, mUnary, productNM⟩ (hsame_symm sameProduct)).right

theorem crtForward_left_val {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : ZMod (crtModulus m n)) :
    hsame (crtForward mUnary nUnary mNonempty nNonempty x).1.val
      (natModFn m x.val) := by
  rfl

theorem crtForward_right_val {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : ZMod (crtModulus m n)) :
    hsame (crtForward mUnary nUnary mNonempty nNonempty x).2.val
      (natModFn n x.val) := by
  rfl

theorem crtForward_left_of_inverse_raw_mod
    {m n raw : BHist} (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (rawUnary : UnaryHistory raw) :
    hsame
      (natModFn m (natModFn (crtModulus m n) raw))
      (natModFn m raw) :=
  natModFn_rem_rem_of_dvd mUnary mNonempty
    (crtModulus_unary mUnary nUnary)
    (crtProductNonempty mUnary nUnary mNonempty nNonempty)
    rawUnary
    (crtModulus_left_divides mUnary nUnary)

theorem crtForward_right_of_inverse_raw_mod
    {m n raw : BHist} (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (rawUnary : UnaryHistory raw) :
    hsame
      (natModFn n (natModFn (crtModulus m n) raw))
      (natModFn n raw) :=
  natModFn_rem_rem_of_dvd nUnary nNonempty
    (crtModulus_unary mUnary nUnary)
    (crtProductNonempty mUnary nUnary mNonempty nNonempty)
    rawUnary
    (crtModulus_right_divides mUnary nUnary)

theorem crtReconstructPair_unary_readback {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (a : ZMod m) (b : ZMod n) :
    UnaryHistory
      (BEDC.FKernel.Cont.append (crtReconstructPair m n a b).1
        (natComplementMod (crtModulus m n) (crtReconstructPair m n a b).2)) :=
  unary_append_closed
    (crtReconstructPair_carrier mUnary nUnary a b).left
    (natComplementMod_unary (crtModulus_unary mUnary nUnary))

theorem natModFn_add_dvd_tail {M a t : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (tUnary : UnaryHistory t)
    (dividesT : NatDivides M t) :
    hsame (natModFn M (BEDC.FKernel.Cont.append a t)) (natModFn M a) := by
  have tailZero : hsame (natModFn M t) BHist.Empty :=
    (dvd_iff_mod_zero MUnary MNonempty tUnary).mp dividesT
  have addCongr :
      hsame (natModFn M (BEDC.FKernel.Cont.append a t))
        (natModFn M (BEDC.FKernel.Cont.append a BHist.Empty)) :=
    natModFn_add_congruence MUnary MNonempty
      aUnary tUnary aUnary unary_empty
      (hsame_refl _) tailZero
  exact hsame_trans addCongr
    (natModFn_hsame_arg_transport (M := M) (append_empty_right a))

theorem crtAppend_hsame_transport {a b c d : BHist} :
    hsame a b -> hsame c d ->
      hsame (BEDC.FKernel.Cont.append a c) (BEDC.FKernel.Cont.append b d) := by
  intro sameA sameC
  cases sameA
  cases sameC
  rfl

theorem natModFn_add_dvd_head {M a t : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (tUnary : UnaryHistory t)
    (dividesT : NatDivides M t) :
    hsame (natModFn M (BEDC.FKernel.Cont.append t a)) (natModFn M a) := by
  have commuted :
      hsame (natModFn M (BEDC.FKernel.Cont.append t a))
        (natModFn M (BEDC.FKernel.Cont.append a t)) :=
    natModFn_hsame_arg_transport (M := M)
      (unary_append_comm tUnary aUnary)
  exact hsame_trans commuted
    (natModFn_add_dvd_tail MUnary MNonempty aUnary tUnary dividesT)

theorem natModFn_mul_congruence {M a b c d : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (bUnary : UnaryHistory b)
    (cUnary : UnaryHistory c) (dUnary : UnaryHistory d)
    (sameA : hsame (natModFn M a) (natModFn M c))
    (sameB : hsame (natModFn M b) (natModFn M d)) :
    hsame (natModFn M (natMulFn a b)) (natModFn M (natMulFn c d)) := by
  have leftReduce :
      hsame (natModFn M (natMulFn a b))
        (natModFn M (natMulFn (natModFn M a) (natModFn M b))) :=
    mod_mul_compat MUnary MNonempty aUnary bUnary
  have middle :
      hsame
        (natModFn M (natMulFn (natModFn M a) (natModFn M b)))
        (natModFn M (natMulFn (natModFn M c) (natModFn M d))) :=
    natModFn_hsame_arg_transport (M := M)
      (natMulFn_hsame_transport sameA sameB)
  have rightReduce :
      hsame
        (natModFn M (natMulFn (natModFn M c) (natModFn M d)))
        (natModFn M (natMulFn c d)) :=
    hsame_symm (mod_mul_compat MUnary MNonempty cUnary dUnary)
  exact hsame_trans leftReduce (hsame_trans middle rightReduce)

theorem natModFn_mul_dvd_left_zero {M a b : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (bUnary : UnaryHistory b)
    (dividesA : NatDivides M a) :
    hsame (natModFn M (natMulFn a b)) BHist.Empty := by
  have productUnary : UnaryHistory (natMulFn a b) :=
    natMulFn_unary aUnary bUnary
  have dividesProduct : NatDivides M (natMulFn a b) :=
    NatDivides_mul_right_factor_closed bUnary dividesA
      (natMulFn_rel aUnary bUnary)
  exact (dvd_iff_mod_zero MUnary MNonempty productUnary).mp dividesProduct

theorem natModFn_mul_dvd_right_zero {M a b : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (bUnary : UnaryHistory b)
    (dividesB : NatDivides M b) :
    hsame (natModFn M (natMulFn a b)) BHist.Empty := by
  have commuted :
      hsame (natModFn M (natMulFn a b))
        (natModFn M (natMulFn b a)) :=
    natModFn_hsame_arg_transport (M := M)
      (natMulFn_comm_hsame aUnary bUnary)
  exact hsame_trans commuted
    (natModFn_mul_dvd_left_zero MUnary MNonempty bUnary aUnary dividesB)

theorem natMulFn_empty_left_zero {a : BHist}
    (aUnary : UnaryHistory a) :
    hsame (natMulFn BHist.Empty a) BHist.Empty :=
  NatMul_empty_left_result_empty (natMulFn_rel unary_empty aUnary)

theorem natMulFn_empty_right_zero {a : BHist} :
    hsame (natMulFn a BHist.Empty) BHist.Empty := by
  rfl

theorem natMulFn_unit_right_same {a : BHist}
    (aUnary : UnaryHistory a) :
    hsame (natMulFn a NatOne) a :=
  NatMul_unit_right_hsame
    (natMulFn_rel aUnary (unary_e1_closed unary_empty))

theorem pairMul_right_components_divisible {M : BHist} {c p : BHist × BHist}
    (cCarrier : IntPairCarrier c.1 c.2)
    (pCarrier : IntPairCarrier p.1 p.2)
    (dividesP1 : NatDivides M p.1)
    (dividesP2 : NatDivides M p.2) :
    NatDivides M (pairMul c p).1 ∧ NatDivides M (pairMul c p).2 := by
  unfold pairMul
  have leftPosDiv :
      NatDivides M (natMulFn c.1 p.1) :=
    NatDivides_mul_left_closed cCarrier.left dividesP1
      (natMulFn_rel cCarrier.left pCarrier.left)
  have rightPosDiv :
      NatDivides M (natMulFn c.2 p.2) :=
    NatDivides_mul_left_closed cCarrier.right dividesP2
      (natMulFn_rel cCarrier.right pCarrier.right)
  have leftNegDiv :
      NatDivides M (natMulFn c.1 p.2) :=
    NatDivides_mul_left_closed cCarrier.left dividesP2
      (natMulFn_rel cCarrier.left pCarrier.right)
  have rightNegDiv :
      NatDivides M (natMulFn c.2 p.1) :=
    NatDivides_mul_left_closed cCarrier.right dividesP1
      (natMulFn_rel cCarrier.right pCarrier.left)
  constructor
  · exact NatDivides_cont_closed leftPosDiv rightPosDiv (cont_intro rfl)
  · exact NatDivides_cont_closed leftNegDiv rightNegDiv (cont_intro rfl)

theorem pairMul_nat_left_pos_hsame {a : BHist} {p : BHist × BHist}
    (_aUnary : UnaryHistory a) (pCarrier : IntPairCarrier p.1 p.2) :
    hsame (pairMul (a, BHist.Empty) p).1 (natMulFn a p.1) := by
  unfold pairMul
  exact hsame_trans
    (crtAppend_hsame_transport (hsame_refl _)
      (natMulFn_empty_left_zero pCarrier.right))
    (append_empty_right (natMulFn a p.1))

theorem pairMul_nat_left_neg_hsame {a : BHist} {p : BHist × BHist}
    (_aUnary : UnaryHistory a) (pCarrier : IntPairCarrier p.1 p.2) :
    hsame (pairMul (a, BHist.Empty) p).2 (natMulFn a p.2) := by
  unfold pairMul
  exact hsame_trans
    (crtAppend_hsame_transport (hsame_refl _)
      (natMulFn_empty_left_zero pCarrier.left))
    (append_empty_right (natMulFn a p.2))

theorem pairMul_nat_right_components_divisible {M : BHist} {x : BHist × BHist}
    {a : BHist}
    (xCarrier : IntPairCarrier x.1 x.2) (aUnary : UnaryHistory a)
    (dividesA : NatDivides M a) :
    NatDivides M (pairMul x (a, BHist.Empty)).1 ∧
      NatDivides M (pairMul x (a, BHist.Empty)).2 := by
  have zeroDivides : NatDivides M BHist.Empty :=
    NatDivides_empty_right_iff.mpr (NatDivides_divisor_unary dividesA)
  exact pairMul_right_components_divisible xCarrier
    ⟨aUnary, unary_empty⟩ dividesA zeroDivides

theorem natModFn_mul_left_rem_of_factor {M D E x q r c : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (DUnary : UnaryHistory D) (EUnary : UnaryHistory E)
    (cUnary : UnaryHistory c)
    (divrem : NatDivRem D x q r)
    (dividesC : NatDivides E c)
    (productDE : NatMul D E M) :
    hsame (natModFn M (natMulFn x c))
      (natModFn M (natMulFn r c)) := by
  cases divrem with
  | intro dq data =>
      have qUnary : UnaryHistory q := NatMul_right_unary data.left
      have dqUnary : UnaryHistory dq := NatMul_result_unary DUnary data.left
      have rUnary : UnaryHistory r := NatAdd_right_unary data.right.left
      have xAsAppend : hsame x (BEDC.FKernel.Cont.append dq r) :=
        data.right.left.right.right
      have leftTransport :
          hsame (natModFn M (natMulFn x c))
            (natModFn M (natMulFn (BEDC.FKernel.Cont.append dq r) c)) :=
        natModFn_hsame_arg_transport (M := M)
          (natMulFn_hsame_transport xAsAppend (hsame_refl c))
      have distrib :
          hsame
            (natModFn M (natMulFn (BEDC.FKernel.Cont.append dq r) c))
            (natModFn M
              (BEDC.FKernel.Cont.append (natMulFn dq c) (natMulFn r c))) :=
        natModFn_hsame_arg_transport (M := M)
          (natMulFn_append_right_distrib_hsame dqUnary rUnary cUnary)
      have dividesDq : NatDivides D dq :=
        ⟨q, qUnary, data.left⟩
      have headDivides : NatDivides M (natMulFn dq c) :=
        NatDivides_product_closed DUnary EUnary dqUnary cUnary
          dividesDq dividesC productDE (natMulFn_rel dqUnary cUnary)
      have drop :
          hsame
            (natModFn M
              (BEDC.FKernel.Cont.append (natMulFn dq c) (natMulFn r c)))
            (natModFn M (natMulFn r c)) :=
        natModFn_add_dvd_head MUnary MNonempty
          (natMulFn_unary rUnary cUnary)
          (natMulFn_unary dqUnary cUnary)
          headDivides
      exact hsame_trans leftTransport (hsame_trans distrib drop)

theorem pairMul_nat_left_rem_factor_mod_components
    {M D E x q r : BHist} {p : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (DUnary : UnaryHistory D) (EUnary : UnaryHistory E)
    (divrem : NatDivRem D x q r)
    (pCarrier : IntPairCarrier p.1 p.2)
    (dividesP1 : NatDivides E p.1) (dividesP2 : NatDivides E p.2)
    (productDE : NatMul D E M) :
    hsame (natModFn M (pairMul (r, BHist.Empty) p).1)
      (natModFn M (pairMul (x, BHist.Empty) p).1) ∧
        hsame (natModFn M (pairMul (r, BHist.Empty) p).2)
          (natModFn M (pairMul (x, BHist.Empty) p).2) := by
  have xUnary : UnaryHistory x := NatDivRem_dividend_unary divrem
  have rUnary : UnaryHistory r := NatDivRem_remainder_unary divrem
  constructor
  · have remMul :
        hsame (natModFn M (natMulFn x p.1))
          (natModFn M (natMulFn r p.1)) :=
      natModFn_mul_left_rem_of_factor MUnary MNonempty DUnary EUnary
        pCarrier.left divrem dividesP1 productDE
    have rPos :
        hsame (natModFn M (pairMul (r, BHist.Empty) p).1)
          (natModFn M (natMulFn r p.1)) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_pos_hsame rUnary pCarrier)
    have xPos :
        hsame (natModFn M (pairMul (x, BHist.Empty) p).1)
          (natModFn M (natMulFn x p.1)) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_pos_hsame xUnary pCarrier)
    exact hsame_trans rPos
      (hsame_trans (hsame_symm remMul) (hsame_symm xPos))
  · have remMul :
        hsame (natModFn M (natMulFn x p.2))
          (natModFn M (natMulFn r p.2)) :=
      natModFn_mul_left_rem_of_factor MUnary MNonempty DUnary EUnary
        pCarrier.right divrem dividesP2 productDE
    have rNeg :
        hsame (natModFn M (pairMul (r, BHist.Empty) p).2)
          (natModFn M (natMulFn r p.2)) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_neg_hsame rUnary pCarrier)
    have xNeg :
        hsame (natModFn M (pairMul (x, BHist.Empty) p).2)
          (natModFn M (natMulFn x p.2)) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_neg_hsame xUnary pCarrier)
    exact hsame_trans rNeg
      (hsame_trans (hsame_symm remMul) (hsame_symm xNeg))

theorem pairAdd_component_mod_congruence {M : BHist}
    {l r l' r' : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (lCarrier : IntPairCarrier l.1 l.2) (rCarrier : IntPairCarrier r.1 r.2)
    (l'Carrier : IntPairCarrier l'.1 l'.2)
    (r'Carrier : IntPairCarrier r'.1 r'.2)
    (sameL1 : hsame (natModFn M l.1) (natModFn M l'.1))
    (sameL2 : hsame (natModFn M l.2) (natModFn M l'.2))
    (sameR1 : hsame (natModFn M r.1) (natModFn M r'.1))
    (sameR2 : hsame (natModFn M r.2) (natModFn M r'.2)) :
    hsame (natModFn M (pairAdd l r).1)
      (natModFn M (pairAdd l' r').1) ∧
        hsame (natModFn M (pairAdd l r).2)
          (natModFn M (pairAdd l' r').2) := by
  constructor
  · unfold pairAdd
    exact natModFn_add_congruence MUnary MNonempty
      lCarrier.left rCarrier.left l'Carrier.left r'Carrier.left
      sameL1 sameR1
  · unfold pairAdd
    exact natModFn_add_congruence MUnary MNonempty
      lCarrier.right rCarrier.right l'Carrier.right r'Carrier.right
      sameL2 sameR2

theorem pairMul_nat_left_add_mod_components {M a : BHist}
    {p q : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (pCarrier : IntPairCarrier p.1 p.2)
    (qCarrier : IntPairCarrier q.1 q.2) :
    hsame
      (natModFn M
        (pairAdd (pairMul (a, BHist.Empty) p)
          (pairMul (a, BHist.Empty) q)).1)
      (natModFn M (pairMul (a, BHist.Empty) (pairAdd p q)).1) ∧
        hsame
          (natModFn M
            (pairAdd (pairMul (a, BHist.Empty) p)
              (pairMul (a, BHist.Empty) q)).2)
          (natModFn M (pairMul (a, BHist.Empty) (pairAdd p q)).2) := by
  have apCarrier :
      IntPairCarrier (pairMul (a, BHist.Empty) p).1
        (pairMul (a, BHist.Empty) p).2 :=
    pairMul_carrier ⟨aUnary, unary_empty⟩ pCarrier
  have aqCarrier :
      IntPairCarrier (pairMul (a, BHist.Empty) q).1
        (pairMul (a, BHist.Empty) q).2 :=
    pairMul_carrier ⟨aUnary, unary_empty⟩ qCarrier
  have pqCarrier : IntPairCarrier (pairAdd p q).1 (pairAdd p q).2 :=
    pairAdd_carrier pCarrier qCarrier
  constructor
  · have leftReduce :
        hsame
          (natModFn M
            (pairAdd (pairMul (a, BHist.Empty) p)
              (pairMul (a, BHist.Empty) q)).1)
          (natModFn M
            (BEDC.FKernel.Cont.append
              (natMulFn a p.1) (natMulFn a q.1))) := by
      unfold pairAdd
      exact natModFn_add_congruence MUnary MNonempty
        apCarrier.left aqCarrier.left
        (natMulFn_unary aUnary pCarrier.left)
        (natMulFn_unary aUnary qCarrier.left)
        (natModFn_hsame_arg_transport (M := M)
          (pairMul_nat_left_pos_hsame aUnary pCarrier))
        (natModFn_hsame_arg_transport (M := M)
          (pairMul_nat_left_pos_hsame aUnary qCarrier))
    have distrib :
        hsame
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append p.1 q.1)))
          (natModFn M
            (BEDC.FKernel.Cont.append
              (natMulFn a p.1) (natMulFn a q.1))) :=
      natModFn_mul_add_distrib MUnary MNonempty aUnary pCarrier.left qCarrier.left
    have rightReduce :
        hsame
          (natModFn M (pairMul (a, BHist.Empty) (pairAdd p q)).1)
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append p.1 q.1))) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_pos_hsame aUnary pqCarrier)
    exact hsame_trans leftReduce
      (hsame_trans (hsame_symm distrib) (hsame_symm rightReduce))
  · have leftReduce :
        hsame
          (natModFn M
            (pairAdd (pairMul (a, BHist.Empty) p)
              (pairMul (a, BHist.Empty) q)).2)
          (natModFn M
            (BEDC.FKernel.Cont.append
              (natMulFn a p.2) (natMulFn a q.2))) := by
      unfold pairAdd
      exact natModFn_add_congruence MUnary MNonempty
        apCarrier.right aqCarrier.right
        (natMulFn_unary aUnary pCarrier.right)
        (natMulFn_unary aUnary qCarrier.right)
        (natModFn_hsame_arg_transport (M := M)
          (pairMul_nat_left_neg_hsame aUnary pCarrier))
        (natModFn_hsame_arg_transport (M := M)
          (pairMul_nat_left_neg_hsame aUnary qCarrier))
    have distrib :
        hsame
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append p.2 q.2)))
          (natModFn M
            (BEDC.FKernel.Cont.append
              (natMulFn a p.2) (natMulFn a q.2))) :=
      natModFn_mul_add_distrib MUnary MNonempty aUnary pCarrier.right qCarrier.right
    have rightReduce :
        hsame
          (natModFn M (pairMul (a, BHist.Empty) (pairAdd p q)).2)
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append p.2 q.2))) :=
      natModFn_hsame_arg_transport (M := M)
        (pairMul_nat_left_neg_hsame aUnary pqCarrier)
    exact hsame_trans leftReduce
      (hsame_trans (hsame_symm distrib) (hsame_symm rightReduce))

theorem pair_mod_nat_transport_of_component_mod {M a : BHist}
    {p q : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (pCarrier : IntPairCarrier p.1 p.2)
    (qCarrier : IntPairCarrier q.1 q.2)
    (samePos : hsame (natModFn M p.1) (natModFn M q.1))
    (sameNeg : hsame (natModFn M p.2) (natModFn M q.2))
    (qCongr :
      hsame (natModFn M q.1)
        (natModFn M (BEDC.FKernel.Cont.append a q.2))) :
    hsame (natModFn M p.1)
      (natModFn M (BEDC.FKernel.Cont.append a p.2)) := by
  have tail :
      hsame (natModFn M (BEDC.FKernel.Cont.append a q.2))
        (natModFn M (BEDC.FKernel.Cont.append a p.2)) :=
    natModFn_add_congruence MUnary MNonempty
      aUnary qCarrier.right aUnary pCarrier.right
      (hsame_refl _) (hsame_symm sameNeg)
  exact hsame_trans samePos (hsame_trans qCongr tail)

theorem pairAdd_left_divisible_pair_mod_congruence {M a : BHist}
    {l r : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (lCarrier : IntPairCarrier l.1 l.2) (rCarrier : IntPairCarrier r.1 r.2)
    (dividesL1 : NatDivides M l.1) (dividesL2 : NatDivides M l.2)
    (sameR :
      hsame (natModFn M r.1)
        (natModFn M (BEDC.FKernel.Cont.append a r.2))) :
    hsame (natModFn M (pairAdd l r).1)
      (natModFn M (BEDC.FKernel.Cont.append a (pairAdd l r).2)) := by
  unfold pairAdd
  have leftDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.1 r.1))
        (natModFn M r.1) :=
    natModFn_add_dvd_head MUnary MNonempty rCarrier.left lCarrier.left dividesL1
  have lr2Unary : UnaryHistory (BEDC.FKernel.Cont.append l.2 r.2) :=
    unary_append_closed lCarrier.right rCarrier.right
  have rightTailDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.2 r.2))
        (natModFn M r.2) :=
    natModFn_add_dvd_head MUnary MNonempty rCarrier.right lCarrier.right dividesL2
  have rightDrop :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append l.2 r.2)))
        (natModFn M (BEDC.FKernel.Cont.append a r.2)) :=
    natModFn_add_congruence MUnary MNonempty
      aUnary lr2Unary aUnary rCarrier.right
      (hsame_refl _) rightTailDrop
  exact hsame_trans leftDrop
    (hsame_trans sameR (hsame_symm rightDrop))

theorem pairAdd_right_divisible_pair_mod_congruence {M a : BHist}
    {l r : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (lCarrier : IntPairCarrier l.1 l.2) (rCarrier : IntPairCarrier r.1 r.2)
    (dividesR1 : NatDivides M r.1) (dividesR2 : NatDivides M r.2)
    (sameL :
      hsame (natModFn M l.1)
        (natModFn M (BEDC.FKernel.Cont.append a l.2))) :
    hsame (natModFn M (pairAdd l r).1)
      (natModFn M (BEDC.FKernel.Cont.append a (pairAdd l r).2)) := by
  unfold pairAdd
  have leftDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.1 r.1))
        (natModFn M l.1) :=
    natModFn_add_dvd_tail MUnary MNonempty lCarrier.left rCarrier.left dividesR1
  have al2Unary : UnaryHistory (BEDC.FKernel.Cont.append a l.2) :=
    unary_append_closed aUnary lCarrier.right
  have assocRight :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append l.2 r.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a l.2) r.2)) :=
    natModFn_hsame_arg_transport (M := M)
      (hsame_symm (append_assoc a l.2 r.2))
  have rightTailDrop :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a l.2) r.2))
        (natModFn M (BEDC.FKernel.Cont.append a l.2)) :=
    natModFn_add_dvd_tail MUnary MNonempty al2Unary rCarrier.right dividesR2
  exact hsame_trans leftDrop
    (hsame_trans sameL
      (hsame_symm (hsame_trans assocRight rightTailDrop)))

theorem pairAdd_left_divisible_pair_mod_congruence_reflect {M a : BHist}
    {l r : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (lCarrier : IntPairCarrier l.1 l.2) (rCarrier : IntPairCarrier r.1 r.2)
    (dividesL1 : NatDivides M l.1) (dividesL2 : NatDivides M l.2)
    (sameSum :
      hsame (natModFn M (pairAdd l r).1)
        (natModFn M (BEDC.FKernel.Cont.append a (pairAdd l r).2))) :
    hsame (natModFn M r.1)
      (natModFn M (BEDC.FKernel.Cont.append a r.2)) := by
  unfold pairAdd at sameSum
  have leftDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.1 r.1))
        (natModFn M r.1) :=
    natModFn_add_dvd_head MUnary MNonempty rCarrier.left lCarrier.left dividesL1
  have lr2Unary : UnaryHistory (BEDC.FKernel.Cont.append l.2 r.2) :=
    unary_append_closed lCarrier.right rCarrier.right
  have rightTailDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.2 r.2))
        (natModFn M r.2) :=
    natModFn_add_dvd_head MUnary MNonempty rCarrier.right lCarrier.right dividesL2
  have rightDrop :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append l.2 r.2)))
        (natModFn M (BEDC.FKernel.Cont.append a r.2)) :=
    natModFn_add_congruence MUnary MNonempty
      aUnary lr2Unary aUnary rCarrier.right
      (hsame_refl _) rightTailDrop
  exact hsame_trans (hsame_symm leftDrop)
    (hsame_trans sameSum rightDrop)

theorem pairAdd_right_divisible_pair_mod_congruence_reflect {M a : BHist}
    {l r : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a)
    (lCarrier : IntPairCarrier l.1 l.2) (rCarrier : IntPairCarrier r.1 r.2)
    (dividesR1 : NatDivides M r.1) (dividesR2 : NatDivides M r.2)
    (sameSum :
      hsame (natModFn M (pairAdd l r).1)
        (natModFn M (BEDC.FKernel.Cont.append a (pairAdd l r).2))) :
    hsame (natModFn M l.1)
      (natModFn M (BEDC.FKernel.Cont.append a l.2)) := by
  unfold pairAdd at sameSum
  have leftDrop :
      hsame (natModFn M (BEDC.FKernel.Cont.append l.1 r.1))
        (natModFn M l.1) :=
    natModFn_add_dvd_tail MUnary MNonempty lCarrier.left rCarrier.left dividesR1
  have al2Unary : UnaryHistory (BEDC.FKernel.Cont.append a l.2) :=
    unary_append_closed aUnary lCarrier.right
  have assocRight :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append l.2 r.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a l.2) r.2)) :=
    natModFn_hsame_arg_transport (M := M)
      (hsame_symm (append_assoc a l.2 r.2))
  have rightTailDrop :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a l.2) r.2))
        (natModFn M (BEDC.FKernel.Cont.append a l.2)) :=
    natModFn_add_dvd_tail MUnary MNonempty al2Unary rCarrier.right dividesR2
  exact hsame_trans (hsame_symm leftDrop)
    (hsame_trans sameSum
      (hsame_trans assocRight rightTailDrop))

theorem natModFn_of_unit_pair_classifier {M : BHist} {p : BHist × BHist}
    (classified : IntPairClassifier p (NatOne, BHist.Empty)) :
    hsame (natModFn M p.1)
      (natModFn M (BEDC.FKernel.Cont.append NatOne p.2)) := by
  have raw :
      hsame p.1 (BEDC.FKernel.Cont.append NatOne p.2) := by
    have left :
        hsame p.1 (BEDC.FKernel.Cont.append p.1 BHist.Empty) :=
      hsame_symm (append_empty_right p.1)
    exact hsame_trans left classified.right.right
  exact natModFn_hsame_arg_transport (M := M) raw

theorem natModFn_of_nat_pair_classifier {M a : BHist} {p : BHist × BHist}
    (classified : IntPairClassifier p (a, BHist.Empty)) :
    hsame (natModFn M p.1)
      (natModFn M (BEDC.FKernel.Cont.append a p.2)) := by
  have raw :
      hsame p.1 (BEDC.FKernel.Cont.append a p.2) := by
    have left :
        hsame p.1 (BEDC.FKernel.Cont.append p.1 BHist.Empty) :=
      hsame_symm (append_empty_right p.1)
    exact hsame_trans left classified.right.right
  exact natModFn_hsame_arg_transport (M := M) raw

theorem crtBezoutUnit_classifier {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (coprime : hsame (natGcdFn m n) NatOne) :
    IntPairClassifier
      (pairAdd
        (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
        (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)))
      (NatOne, BHist.Empty) := by
  have bezout := natBezoutFn_spec mUnary nUnary
  unfold crtBezoutCoeffs
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    bezout.right.right
    (show IntPairClassifier (natGcdFn m n, BHist.Empty) (NatOne, BHist.Empty) from
      ⟨⟨NatGcd_result_unary (natGcdFn_spec mUnary nUnary), unary_empty⟩,
        ⟨unary_e1_closed unary_empty, unary_empty⟩,
        crtAppend_hsame_transport coprime (hsame_refl _)⟩)

theorem natModFn_of_coprime_bezout_pair {M m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (coprime : hsame (natGcdFn m n) NatOne) :
    hsame
      (natModFn M
        (pairAdd
          (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
          (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).1)
      (natModFn M
        (BEDC.FKernel.Cont.append NatOne
          (pairAdd
            (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
            (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).2)) := by
  exact natModFn_of_unit_pair_classifier (M := M)
    (crtBezoutUnit_classifier mUnary nUnary coprime)

theorem pairMul_nat_left_unit_mod_congruence {M a : BHist}
    {p : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (pCarrier : IntPairCarrier p.1 p.2)
    (sameP :
      hsame (natModFn M p.1)
        (natModFn M (BEDC.FKernel.Cont.append NatOne p.2))) :
    hsame (natModFn M (pairMul (a, BHist.Empty) p).1)
      (natModFn M
        (BEDC.FKernel.Cont.append a (pairMul (a, BHist.Empty) p).2)) := by
  have natOneUnary : UnaryHistory NatOne := unary_e1_closed unary_empty
  have p1Unary : UnaryHistory p.1 := pCarrier.left
  have p2Unary : UnaryHistory p.2 := pCarrier.right
  have unitP2Unary : UnaryHistory (BEDC.FKernel.Cont.append NatOne p.2) :=
    unary_append_closed natOneUnary p2Unary
  have coreCongr :
      hsame (natModFn M (natMulFn a p.1))
        (natModFn M (natMulFn a (BEDC.FKernel.Cont.append NatOne p.2))) :=
    natModFn_mul_congruence MUnary MNonempty
      aUnary p1Unary aUnary unitP2Unary
      (hsame_refl _) sameP
  have distrib :
      hsame
        (natModFn M (natMulFn a (BEDC.FKernel.Cont.append NatOne p.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append (natMulFn a NatOne) (natMulFn a p.2))) :=
    natModFn_mul_add_distrib MUnary MNonempty aUnary natOneUnary p2Unary
  have unitLeft :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append (natMulFn a NatOne) (natMulFn a p.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append a (natMulFn a p.2))) :=
    natModFn_hsame_arg_transport (M := M)
      (crtAppend_hsame_transport (natMulFn_unit_right_same aUnary) (hsame_refl _))
  have posActual :
      hsame (pairMul (a, BHist.Empty) p).1 (natMulFn a p.1) := by
    unfold pairMul
    exact hsame_trans
      (crtAppend_hsame_transport (hsame_refl _) (natMulFn_empty_left_zero p2Unary))
      (append_empty_right (natMulFn a p.1))
  have negActual :
      hsame (pairMul (a, BHist.Empty) p).2 (natMulFn a p.2) := by
    unfold pairMul
    exact hsame_trans
      (crtAppend_hsame_transport (hsame_refl _) (natMulFn_empty_left_zero p1Unary))
      (append_empty_right (natMulFn a p.2))
  have core :
      hsame (natModFn M (natMulFn a p.1))
        (natModFn M (BEDC.FKernel.Cont.append a (natMulFn a p.2))) :=
    hsame_trans coreCongr (hsame_trans distrib unitLeft)
  exact hsame_trans
    (natModFn_hsame_arg_transport (M := M) posActual)
    (hsame_trans core
      (hsame_symm
        (natModFn_hsame_arg_transport (M := M)
          (crtAppend_hsame_transport (hsame_refl _) negActual))))

theorem natDivides_complement_sum {M r : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (rUnary : UnaryHistory r) :
    NatDivides M (BEDC.FKernel.Cont.append r (natComplementMod M r)) := by
  have compUnary : UnaryHistory (natComplementMod M r) :=
    natComplementMod_unary MUnary
  have remUnary : UnaryHistory (natModFn M r) :=
    natModFn_unary MUnary rUnary MNonempty
  have reduceHead :
      hsame
        (natModFn M (BEDC.FKernel.Cont.append r (natComplementMod M r)))
        (natModFn M
          (BEDC.FKernel.Cont.append (natModFn M r) (natComplementMod M r))) :=
    natModFn_add_congruence MUnary MNonempty
      rUnary compUnary remUnary compUnary
      (hsame_symm (mod_idem MUnary MNonempty rUnary))
      (hsame_refl _)
  have sumZero :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append (natModFn M r) (natComplementMod M r)))
        BHist.Empty :=
    natComplementMod_add_left_zero MUnary MNonempty rUnary
  exact (dvd_iff_mod_zero MUnary MNonempty
    (unary_append_closed rUnary compUnary)).mpr
      (hsame_trans reduceHead sumZero)

theorem crtPairResidue_add_dvd_tail {M a t : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (tUnary : UnaryHistory t)
    (aStrict : NatUnaryStrictPrefix a M)
    (dividesT : NatDivides M t) :
    hsame
      (crtPairResidue M (BEDC.FKernel.Cont.append a t, BHist.Empty))
      a := by
  unfold crtPairResidue
  have atUnary : UnaryHistory (BEDC.FKernel.Cont.append a t) :=
    unary_append_closed aUnary tUnary
  have raw :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a t)
            (natComplementMod M BHist.Empty)))
        (natModFn M (BEDC.FKernel.Cont.append a t)) := by
    have zeroMod : hsame (natModFn M BHist.Empty) BHist.Empty := by
      unfold natModFn natDivRemFn
      rfl
    have subSame : hsame (natSubUnary M (natModFn M BHist.Empty)) M := by
      exact hsame_trans
        (by
          cases zeroMod
          exact natSubUnary_empty_right MUnary)
        (hsame_refl M)
    have compEmptyZero :
        hsame (natComplementMod M BHist.Empty) BHist.Empty := by
      unfold natComplementMod
      exact hsame_trans
        (natModFn_hsame_arg_transport (M := M) subSame)
        (natModFn_self_zero MUnary MNonempty)
    exact natModFn_hsame_arg_transport (M := M)
      (by
        exact hsame_trans
          (cont_respects_hsame (hsame_refl _) compEmptyZero
            (cont_intro rfl) (cont_right_unit _))
          (cont_right_unit_iff.mp (cont_right_unit _)))
  exact hsame_trans raw
    (hsame_trans
      (natModFn_add_dvd_tail MUnary MNonempty aUnary tUnary dividesT)
      (natModFn_of_strict MUnary MNonempty aUnary aStrict))

theorem natComplementMod_of_mod_zero {M t : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (modZero : hsame (natModFn M t) BHist.Empty) :
    hsame (natComplementMod M t) BHist.Empty := by
  unfold natComplementMod
  have subSame : hsame (natSubUnary M (natModFn M t)) M := by
    rw [modZero]
    exact natSubUnary_empty_right MUnary
  exact hsame_trans
    (natModFn_hsame_arg_transport (M := M) subSame)
    (natModFn_self_zero MUnary MNonempty)

theorem crtPairResidue_add_divisible_pair {M a t u : BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (tUnary : UnaryHistory t) (uUnary : UnaryHistory u)
    (aStrict : NatUnaryStrictPrefix a M)
    (dividesT : NatDivides M t) (dividesU : NatDivides M u) :
    hsame
      (crtPairResidue M (BEDC.FKernel.Cont.append a t, u))
      a := by
  have uZero : hsame (natModFn M u) BHist.Empty :=
    (dvd_iff_mod_zero MUnary MNonempty uUnary).mp dividesU
  have compUZero : hsame (natComplementMod M u) BHist.Empty :=
    natComplementMod_of_mod_zero MUnary MNonempty uZero
  have raw :
      hsame
        (crtPairResidue M (BEDC.FKernel.Cont.append a t, u))
        (crtPairResidue M (BEDC.FKernel.Cont.append a t, BHist.Empty)) := by
    unfold crtPairResidue
    change hsame
      (natModFn M
        (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append a t)
          (natComplementMod M u)))
      (natModFn M
        (BEDC.FKernel.Cont.append (BEDC.FKernel.Cont.append a t)
          (natComplementMod M BHist.Empty)))
    have compEmptyZero : hsame (natComplementMod M BHist.Empty) BHist.Empty :=
      natComplementMod_of_mod_zero MUnary MNonempty (by rfl)
    exact natModFn_hsame_arg_transport (M := M)
      (crtAppend_hsame_transport (hsame_refl _)
        (hsame_trans compUZero (hsame_symm compEmptyZero)))
  exact hsame_trans raw
    (crtPairResidue_add_dvd_tail MUnary MNonempty aUnary tUnary
      aStrict dividesT)

theorem crtPairResidue_of_pair_mod_congruence {M a : BHist} {p : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (aUnary : UnaryHistory a) (pCarrier : IntPairCarrier p.1 p.2)
    (aStrict : NatUnaryStrictPrefix a M)
    (samePair :
      hsame (natModFn M p.1)
        (natModFn M (BEDC.FKernel.Cont.append a p.2))) :
    hsame (crtPairResidue M p) a := by
  unfold crtPairResidue
  have p2Unary : UnaryHistory p.2 := pCarrier.right
  have compUnary : UnaryHistory (natComplementMod M p.2) :=
    natComplementMod_unary MUnary
  have aP2Unary : UnaryHistory (BEDC.FKernel.Cont.append a p.2) :=
    unary_append_closed aUnary p2Unary
  have firstStep :
      hsame
        (natModFn M (BEDC.FKernel.Cont.append p.1 (natComplementMod M p.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a p.2) (natComplementMod M p.2))) :=
    natModFn_add_congruence MUnary MNonempty
      pCarrier.left compUnary aP2Unary compUnary
      samePair (hsame_refl _)
  have assocStep :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append
            (BEDC.FKernel.Cont.append a p.2) (natComplementMod M p.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append p.2 (natComplementMod M p.2)))) :=
    natModFn_hsame_arg_transport (M := M)
      (append_assoc a p.2 (natComplementMod M p.2))
  have tailUnary :
      UnaryHistory (BEDC.FKernel.Cont.append p.2 (natComplementMod M p.2)) :=
    unary_append_closed p2Unary compUnary
  have tailDivides :
      NatDivides M (BEDC.FKernel.Cont.append p.2 (natComplementMod M p.2)) :=
    natDivides_complement_sum MUnary MNonempty p2Unary
  have dropTail :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append a
            (BEDC.FKernel.Cont.append p.2 (natComplementMod M p.2))))
        (natModFn M a) :=
    natModFn_add_dvd_tail MUnary MNonempty aUnary tailUnary tailDivides
  exact hsame_trans firstStep
    (hsame_trans assocStep
      (hsame_trans dropTail
        (natModFn_of_strict MUnary MNonempty aUnary aStrict)))

theorem crtPairResidue_reduce_of_dvd {M K : BHist} {p : BHist × BHist}
    (MUnary : UnaryHistory M) (MNonempty : hsame M BHist.Empty -> False)
    (KUnary : UnaryHistory K) (KNonempty : hsame K BHist.Empty -> False)
    (pCarrier : IntPairCarrier p.1 p.2) (dividesMK : NatDivides M K) :
    hsame (natModFn M (crtPairResidue K p)) (crtPairResidue M p) := by
  unfold crtPairResidue
  have compKUnary : UnaryHistory (natComplementMod K p.2) :=
    natComplementMod_unary KUnary
  have compMUnary : UnaryHistory (natComplementMod M p.2) :=
    natComplementMod_unary MUnary
  have rawKUnary :
      UnaryHistory (BEDC.FKernel.Cont.append p.1 (natComplementMod K p.2)) :=
    unary_append_closed pCarrier.left compKUnary
  have reduceOuter :
      hsame
        (natModFn M
          (natModFn K
            (BEDC.FKernel.Cont.append p.1 (natComplementMod K p.2))))
        (natModFn M
          (BEDC.FKernel.Cont.append p.1 (natComplementMod K p.2))) :=
    natModFn_rem_rem_of_dvd MUnary MNonempty KUnary KNonempty rawKUnary dividesMK
  have compKReduce :
      hsame (natModFn M (natComplementMod K p.2))
        (natComplementMod M (natModFn M p.2)) :=
    natComplementMod_reduce_compat_of_dvd MUnary MNonempty KUnary KNonempty
      pCarrier.right dividesMK
  have compMReduce :
      hsame (natModFn M (natComplementMod M p.2))
        (natComplementMod M (natModFn M p.2)) :=
    natComplementMod_reduce_compat_of_dvd MUnary MNonempty MUnary MNonempty
      pCarrier.right (NatDivides_reflexive_pair MUnary).right
  have tailsSame :
      hsame (natModFn M (natComplementMod K p.2))
        (natModFn M (natComplementMod M p.2)) :=
    hsame_trans compKReduce (hsame_symm compMReduce)
  have tailTransport :
      hsame
        (natModFn M
          (BEDC.FKernel.Cont.append p.1 (natComplementMod K p.2)))
        (natModFn M
          (BEDC.FKernel.Cont.append p.1 (natComplementMod M p.2))) :=
    natModFn_add_congruence MUnary MNonempty
      pCarrier.left compKUnary pCarrier.left compMUnary
      (hsame_refl _) tailsSame
  exact hsame_trans reduceOuter tailTransport

theorem crtReconstructPair_left_mod_congruence {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (pair : ZMod m × ZMod n) :
    hsame (natModFn m (crtReconstructPair m n pair.1 pair.2).1)
      (natModFn m
        (BEDC.FKernel.Cont.append pair.1.val
          (crtReconstructPair m n pair.1 pair.2).2)) := by
  have coeffCarrier :
      IntPairCarrier (crtBezoutCoeffs m n).1.1 (crtBezoutCoeffs m n).1.2 ∧
        IntPairCarrier (crtBezoutCoeffs m n).2.1 (crtBezoutCoeffs m n).2.2 := by
    unfold crtBezoutCoeffs
    exact natBezoutFn_carrier mUnary nUnary
  have leftBaseCarrier :
      IntPairCarrier
        (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).1
        (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).2 :=
    pairMul_carrier coeffCarrier.left ⟨mUnary, unary_empty⟩
  have rightBaseCarrier :
      IntPairCarrier
        (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).1
        (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).2 :=
    pairMul_carrier coeffCarrier.right ⟨nUnary, unary_empty⟩
  have mDividesM : NatDivides m m :=
    (NatDivides_reflexive_pair mUnary).right
  have leftBaseDivides :
      NatDivides m
          (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).1 ∧
        NatDivides m
          (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).2 :=
    pairMul_nat_right_components_divisible coeffCarrier.left mUnary mDividesM
  have bezoutMod :
      hsame
        (natModFn m
          (pairAdd
            (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
            (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).1)
        (natModFn m
          (BEDC.FKernel.Cont.append NatOne
            (pairAdd
              (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
              (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).2)) :=
    natModFn_of_coprime_bezout_pair mUnary nUnary coprime
  have rightBaseUnit :
      hsame
        (natModFn m (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).1)
        (natModFn m
          (BEDC.FKernel.Cont.append NatOne
            (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).2)) :=
    pairAdd_left_divisible_pair_mod_congruence_reflect
      mUnary mNonempty (unary_e1_closed unary_empty)
      leftBaseCarrier rightBaseCarrier
      leftBaseDivides.left leftBaseDivides.right bezoutMod
  have rightTermUnit :
      hsame
        (natModFn m
          (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).1)
        (natModFn m
          (BEDC.FKernel.Cont.append pair.1.val
            (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).2)) := by
    unfold crtTermRight
    exact pairMul_nat_left_unit_mod_congruence
      mUnary mNonempty (zmodVal_unary mUnary pair.1) rightBaseCarrier rightBaseUnit
  have leftTermCarrier :
      IntPairCarrier
        (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).1
        (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).2 := by
    unfold crtTermLeft
    exact pairMul_carrier
      ⟨zmodVal_unary nUnary pair.2, unary_empty⟩ leftBaseCarrier
  have rightTermCarrier :
      IntPairCarrier
        (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).1
        (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).2 := by
    unfold crtTermRight
    exact pairMul_carrier
      ⟨zmodVal_unary mUnary pair.1, unary_empty⟩ rightBaseCarrier
  have leftTermDivides :
      NatDivides m
          (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).1 ∧
        NatDivides m
          (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).2 := by
    unfold crtTermLeft
    exact pairMul_right_components_divisible
      ⟨zmodVal_unary nUnary pair.2, unary_empty⟩ leftBaseCarrier
      leftBaseDivides.left leftBaseDivides.right
  have raw :
      hsame
        (natModFn m
          (pairAdd
            (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val)
            (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val)).1)
        (natModFn m
          (BEDC.FKernel.Cont.append pair.1.val
            (pairAdd
              (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val)
              (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val)).2)) :=
    pairAdd_left_divisible_pair_mod_congruence
      mUnary mNonempty (zmodVal_unary mUnary pair.1)
      leftTermCarrier rightTermCarrier
      leftTermDivides.left leftTermDivides.right rightTermUnit
  unfold crtReconstructPair
  exact raw

theorem crtReconstructPair_right_mod_congruence {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (pair : ZMod m × ZMod n) :
    hsame (natModFn n (crtReconstructPair m n pair.1 pair.2).1)
      (natModFn n
        (BEDC.FKernel.Cont.append pair.2.val
          (crtReconstructPair m n pair.1 pair.2).2)) := by
  have coeffCarrier :
      IntPairCarrier (crtBezoutCoeffs m n).1.1 (crtBezoutCoeffs m n).1.2 ∧
        IntPairCarrier (crtBezoutCoeffs m n).2.1 (crtBezoutCoeffs m n).2.2 := by
    unfold crtBezoutCoeffs
    exact natBezoutFn_carrier mUnary nUnary
  have leftBaseCarrier :
      IntPairCarrier
        (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).1
        (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).2 :=
    pairMul_carrier coeffCarrier.left ⟨mUnary, unary_empty⟩
  have rightBaseCarrier :
      IntPairCarrier
        (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).1
        (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).2 :=
    pairMul_carrier coeffCarrier.right ⟨nUnary, unary_empty⟩
  have nDividesN : NatDivides n n :=
    (NatDivides_reflexive_pair nUnary).right
  have rightBaseDivides :
      NatDivides n
          (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).1 ∧
        NatDivides n
          (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)).2 :=
    pairMul_nat_right_components_divisible coeffCarrier.right nUnary nDividesN
  have bezoutMod :
      hsame
        (natModFn n
          (pairAdd
            (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
            (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).1)
        (natModFn n
          (BEDC.FKernel.Cont.append NatOne
            (pairAdd
              (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty))
              (pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty))).2)) :=
    natModFn_of_coprime_bezout_pair mUnary nUnary coprime
  have leftBaseUnit :
      hsame
        (natModFn n (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).1)
        (natModFn n
          (BEDC.FKernel.Cont.append NatOne
            (pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)).2)) :=
    pairAdd_right_divisible_pair_mod_congruence_reflect
      nUnary nNonempty (unary_e1_closed unary_empty)
      leftBaseCarrier rightBaseCarrier
      rightBaseDivides.left rightBaseDivides.right bezoutMod
  have leftTermUnit :
      hsame
        (natModFn n
          (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).1)
        (natModFn n
          (BEDC.FKernel.Cont.append pair.2.val
            (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).2)) := by
    unfold crtTermLeft
    exact pairMul_nat_left_unit_mod_congruence
      nUnary nNonempty (zmodVal_unary nUnary pair.2) leftBaseCarrier leftBaseUnit
  have leftTermCarrier :
      IntPairCarrier
        (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).1
        (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val).2 := by
    unfold crtTermLeft
    exact pairMul_carrier
      ⟨zmodVal_unary nUnary pair.2, unary_empty⟩ leftBaseCarrier
  have rightTermCarrier :
      IntPairCarrier
        (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).1
        (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).2 := by
    unfold crtTermRight
    exact pairMul_carrier
      ⟨zmodVal_unary mUnary pair.1, unary_empty⟩ rightBaseCarrier
  have rightTermDivides :
      NatDivides n
          (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).1 ∧
        NatDivides n
          (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val).2 := by
    unfold crtTermRight
    exact pairMul_right_components_divisible
      ⟨zmodVal_unary mUnary pair.1, unary_empty⟩ rightBaseCarrier
      rightBaseDivides.left rightBaseDivides.right
  have raw :
      hsame
        (natModFn n
          (pairAdd
            (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val)
            (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val)).1)
        (natModFn n
          (BEDC.FKernel.Cont.append pair.2.val
            (pairAdd
              (crtTermLeft m (crtBezoutCoeffs m n).1 pair.2.val)
              (crtTermRight n (crtBezoutCoeffs m n).2 pair.1.val)).2)) :=
    pairAdd_right_divisible_pair_mod_congruence
      nUnary nNonempty (zmodVal_unary nUnary pair.2)
      leftTermCarrier rightTermCarrier
      rightTermDivides.left rightTermDivides.right leftTermUnit
  unfold crtReconstructPair
  exact raw

theorem crt_right_inv_left {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (pair : ZMod m × ZMod n) :
    zmodEq (crtForward mUnary nUnary mNonempty nNonempty
      (crtInverse mUnary nUnary mNonempty nNonempty pair)).1 pair.1 := by
  unfold zmodEq crtForward crtInverse
  change hsame
    (natModFn m (crtPairResidue (crtModulus m n)
      (crtReconstructPair m n pair.1 pair.2)))
    pair.1.val
  have rawCarrier :
      IntPairCarrier (crtReconstructPair m n pair.1 pair.2).1
        (crtReconstructPair m n pair.1 pair.2).2 :=
    crtReconstructPair_carrier mUnary nUnary pair.1 pair.2
  have reduce :
      hsame
        (natModFn m (crtPairResidue (crtModulus m n)
          (crtReconstructPair m n pair.1 pair.2)))
        (crtPairResidue m (crtReconstructPair m n pair.1 pair.2)) :=
    crtPairResidue_reduce_of_dvd mUnary mNonempty
      (crtModulus_unary mUnary nUnary)
      (crtProductNonempty mUnary nUnary mNonempty nNonempty)
      rawCarrier (crtModulus_left_divides mUnary nUnary)
  have residue :
      hsame (crtPairResidue m (crtReconstructPair m n pair.1 pair.2))
        pair.1.val :=
    crtPairResidue_of_pair_mod_congruence
      mUnary mNonempty (zmodVal_unary mUnary pair.1)
      rawCarrier pair.1.isLt
      (crtReconstructPair_left_mod_congruence
        mUnary nUnary mNonempty coprime pair)
  exact hsame_trans reduce residue

theorem crt_right_inv_right {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (pair : ZMod m × ZMod n) :
    zmodEq (crtForward mUnary nUnary mNonempty nNonempty
      (crtInverse mUnary nUnary mNonempty nNonempty pair)).2 pair.2 := by
  unfold zmodEq crtForward crtInverse
  change hsame
    (natModFn n (crtPairResidue (crtModulus m n)
      (crtReconstructPair m n pair.1 pair.2)))
    pair.2.val
  have rawCarrier :
      IntPairCarrier (crtReconstructPair m n pair.1 pair.2).1
        (crtReconstructPair m n pair.1 pair.2).2 :=
    crtReconstructPair_carrier mUnary nUnary pair.1 pair.2
  have reduce :
      hsame
        (natModFn n (crtPairResidue (crtModulus m n)
          (crtReconstructPair m n pair.1 pair.2)))
        (crtPairResidue n (crtReconstructPair m n pair.1 pair.2)) :=
    crtPairResidue_reduce_of_dvd nUnary nNonempty
      (crtModulus_unary mUnary nUnary)
      (crtProductNonempty mUnary nUnary mNonempty nNonempty)
      rawCarrier (crtModulus_right_divides mUnary nUnary)
  have residue :
      hsame (crtPairResidue n (crtReconstructPair m n pair.1 pair.2))
        pair.2.val :=
    crtPairResidue_of_pair_mod_congruence
      nUnary nNonempty (zmodVal_unary nUnary pair.2)
      rawCarrier pair.2.isLt
      (crtReconstructPair_right_mod_congruence
        mUnary nUnary nNonempty coprime pair)
  exact hsame_trans reduce residue

theorem crt_right_inv {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (pair : ZMod m × ZMod n) :
    zmodEq (crtForward mUnary nUnary mNonempty nNonempty
      (crtInverse mUnary nUnary mNonempty nNonempty pair)).1 pair.1 ∧
        zmodEq (crtForward mUnary nUnary mNonempty nNonempty
          (crtInverse mUnary nUnary mNonempty nNonempty pair)).2 pair.2 := by
  constructor
  · exact crt_right_inv_left mUnary nUnary mNonempty nNonempty coprime pair
  · exact crt_right_inv_right mUnary nUnary mNonempty nNonempty coprime pair

theorem crt_left_inv {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne)
    (x : ZMod (crtModulus m n)) :
    zmodEq (crtInverse mUnary nUnary mNonempty nNonempty
      (crtForward mUnary nUnary mNonempty nNonempty x)) x := by
  unfold zmodEq crtInverse crtForward
  change hsame
    (crtPairResidue (crtModulus m n)
      (crtReconstructPair m n
        (zmodFromNat m mUnary mNonempty x.val
          (zmodVal_unary (natMulFn_unary mUnary nUnary) x))
        (zmodFromNat n nUnary nNonempty x.val
          (zmodVal_unary (natMulFn_unary mUnary nUnary) x))))
    x.val
  let M := crtModulus m n
  let xm := zmodFromNat m mUnary mNonempty x.val
    (zmodVal_unary (natMulFn_unary mUnary nUnary) x)
  let xn := zmodFromNat n nUnary nNonempty x.val
    (zmodVal_unary (natMulFn_unary mUnary nUnary) x)
  let leftBase := pairMul (crtBezoutCoeffs m n).1 (m, BHist.Empty)
  let rightBase := pairMul (crtBezoutCoeffs m n).2 (n, BHist.Empty)
  let bezoutSum := pairAdd leftBase rightBase
  let raw := crtReconstructPair m n xm xn
  let target := pairMul (x.val, BHist.Empty) bezoutSum
  have MUnary : UnaryHistory M := crtModulus_unary mUnary nUnary
  have MNonempty : hsame M BHist.Empty -> False :=
    crtProductNonempty mUnary nUnary mNonempty nNonempty
  have xUnary : UnaryHistory x.val :=
    zmodVal_unary MUnary x
  have coeffCarrier :
      IntPairCarrier (crtBezoutCoeffs m n).1.1 (crtBezoutCoeffs m n).1.2 ∧
        IntPairCarrier (crtBezoutCoeffs m n).2.1 (crtBezoutCoeffs m n).2.2 := by
    unfold crtBezoutCoeffs
    exact natBezoutFn_carrier mUnary nUnary
  have leftBaseCarrier :
      IntPairCarrier leftBase.1 leftBase.2 := by
    unfold leftBase
    exact pairMul_carrier coeffCarrier.left ⟨mUnary, unary_empty⟩
  have rightBaseCarrier :
      IntPairCarrier rightBase.1 rightBase.2 := by
    unfold rightBase
    exact pairMul_carrier coeffCarrier.right ⟨nUnary, unary_empty⟩
  have leftBaseDividesByM :
      NatDivides m leftBase.1 ∧ NatDivides m leftBase.2 := by
    unfold leftBase
    exact pairMul_nat_right_components_divisible coeffCarrier.left mUnary
      (NatDivides_reflexive_pair mUnary).right
  have rightBaseDividesByN :
      NatDivides n rightBase.1 ∧ NatDivides n rightBase.2 := by
    unfold rightBase
    exact pairMul_nat_right_components_divisible coeffCarrier.right nUnary
      (NatDivides_reflexive_pair nUnary).right
  have leftTermCarrier :
      IntPairCarrier (crtTermLeft m (crtBezoutCoeffs m n).1 xn.val).1
        (crtTermLeft m (crtBezoutCoeffs m n).1 xn.val).2 := by
    unfold crtTermLeft
    exact pairMul_carrier ⟨zmodVal_unary nUnary xn, unary_empty⟩ leftBaseCarrier
  have rightTermCarrier :
      IntPairCarrier (crtTermRight n (crtBezoutCoeffs m n).2 xm.val).1
        (crtTermRight n (crtBezoutCoeffs m n).2 xm.val).2 := by
    unfold crtTermRight
    exact pairMul_carrier ⟨zmodVal_unary mUnary xm, unary_empty⟩ rightBaseCarrier
  have rawCarrier : IntPairCarrier raw.1 raw.2 := by
    unfold raw
    exact crtReconstructPair_carrier mUnary nUnary xm xn
  have targetCarrier : IntPairCarrier target.1 target.2 := by
    unfold target bezoutSum
    exact pairMul_carrier ⟨xUnary, unary_empty⟩
      (pairAdd_carrier leftBaseCarrier rightBaseCarrier)
  have rightBaseModByM :
      hsame
        (natModFn m rightBase.1)
        (natModFn m
          (BEDC.FKernel.Cont.append NatOne rightBase.2)) := by
    have bezoutMod :
        hsame (natModFn m bezoutSum.1)
          (natModFn m
            (BEDC.FKernel.Cont.append NatOne bezoutSum.2)) := by
      unfold bezoutSum leftBase rightBase
      exact natModFn_of_coprime_bezout_pair mUnary nUnary coprime
    unfold bezoutSum at bezoutMod
    exact pairAdd_left_divisible_pair_mod_congruence_reflect
      mUnary mNonempty (unary_e1_closed unary_empty)
      leftBaseCarrier rightBaseCarrier
      leftBaseDividesByM.left leftBaseDividesByM.right bezoutMod
  have leftBaseModByN :
      hsame
        (natModFn n leftBase.1)
        (natModFn n
          (BEDC.FKernel.Cont.append NatOne leftBase.2)) := by
    have bezoutMod :
        hsame (natModFn n bezoutSum.1)
          (natModFn n
            (BEDC.FKernel.Cont.append NatOne bezoutSum.2)) := by
      unfold bezoutSum leftBase rightBase
      exact natModFn_of_coprime_bezout_pair mUnary nUnary coprime
    unfold bezoutSum at bezoutMod
    exact pairAdd_right_divisible_pair_mod_congruence_reflect
      nUnary nNonempty (unary_e1_closed unary_empty)
      leftBaseCarrier rightBaseCarrier
      rightBaseDividesByN.left rightBaseDividesByN.right bezoutMod
  have leftTermToX :
      hsame (natModFn M (crtTermLeft m (crtBezoutCoeffs m n).1 xn.val).1)
        (natModFn M (pairMul (x.val, BHist.Empty) leftBase).1) ∧
        hsame (natModFn M (crtTermLeft m (crtBezoutCoeffs m n).1 xn.val).2)
          (natModFn M (pairMul (x.val, BHist.Empty) leftBase).2) := by
    unfold crtTermLeft leftBase M
    exact pairMul_nat_left_rem_factor_mod_components
      (crtModulus_unary mUnary nUnary)
      (crtProductNonempty mUnary nUnary mNonempty nNonempty)
      nUnary mUnary
      (natModFn_spec nUnary xUnary nNonempty)
      leftBaseCarrier leftBaseDividesByM.left leftBaseDividesByM.right
      (crtModulus_comm_mul_rel mUnary nUnary)
  have rightTermToX :
      hsame (natModFn M (crtTermRight n (crtBezoutCoeffs m n).2 xm.val).1)
        (natModFn M (pairMul (x.val, BHist.Empty) rightBase).1) ∧
        hsame (natModFn M (crtTermRight n (crtBezoutCoeffs m n).2 xm.val).2)
          (natModFn M (pairMul (x.val, BHist.Empty) rightBase).2) := by
    unfold crtTermRight rightBase M
    exact pairMul_nat_left_rem_factor_mod_components
      (crtModulus_unary mUnary nUnary)
      (crtProductNonempty mUnary nUnary mNonempty nNonempty)
      mUnary nUnary
      (natModFn_spec mUnary xUnary mNonempty)
      rightBaseCarrier rightBaseDividesByN.left rightBaseDividesByN.right
      (crtModulus_mul_rel mUnary nUnary)
  have rawToPairAdd :
      hsame (natModFn M raw.1)
        (natModFn M
          (pairAdd (pairMul (x.val, BHist.Empty) leftBase)
            (pairMul (x.val, BHist.Empty) rightBase)).1) ∧
        hsame (natModFn M raw.2)
          (natModFn M
            (pairAdd (pairMul (x.val, BHist.Empty) leftBase)
              (pairMul (x.val, BHist.Empty) rightBase)).2) := by
    have targetLeftCarrier :
        IntPairCarrier (pairMul (x.val, BHist.Empty) leftBase).1
          (pairMul (x.val, BHist.Empty) leftBase).2 :=
      pairMul_carrier ⟨xUnary, unary_empty⟩ leftBaseCarrier
    have targetRightCarrier :
        IntPairCarrier (pairMul (x.val, BHist.Empty) rightBase).1
          (pairMul (x.val, BHist.Empty) rightBase).2 :=
      pairMul_carrier ⟨xUnary, unary_empty⟩ rightBaseCarrier
    unfold raw crtReconstructPair
    exact pairAdd_component_mod_congruence MUnary MNonempty
      leftTermCarrier rightTermCarrier targetLeftCarrier targetRightCarrier
      leftTermToX.left leftTermToX.right
      rightTermToX.left rightTermToX.right
  have pairAddToTarget :
      hsame
        (natModFn M
          (pairAdd (pairMul (x.val, BHist.Empty) leftBase)
            (pairMul (x.val, BHist.Empty) rightBase)).1)
        (natModFn M target.1) ∧
      hsame
        (natModFn M
          (pairAdd (pairMul (x.val, BHist.Empty) leftBase)
            (pairMul (x.val, BHist.Empty) rightBase)).2)
        (natModFn M target.2) := by
    unfold target bezoutSum
    exact pairMul_nat_left_add_mod_components MUnary MNonempty xUnary
      leftBaseCarrier rightBaseCarrier
  have rawToTarget :
      hsame (natModFn M raw.1) (natModFn M target.1) ∧
      hsame (natModFn M raw.2) (natModFn M target.2) :=
    ⟨hsame_trans rawToPairAdd.left pairAddToTarget.left,
      hsame_trans rawToPairAdd.right pairAddToTarget.right⟩
  have targetCongr :
      hsame (natModFn M target.1)
        (natModFn M (BEDC.FKernel.Cont.append x.val target.2)) := by
    unfold target bezoutSum
    have unitClassified :
        IntPairClassifier bezoutSum (NatOne, BHist.Empty) := by
      unfold bezoutSum leftBase rightBase
      exact crtBezoutUnit_classifier mUnary nUnary coprime
    have mulClassified :
        IntPairClassifier
          (pairMul (x.val, BHist.Empty) bezoutSum)
          (pairMul (x.val, BHist.Empty) (NatOne, BHist.Empty)) :=
      BEDC.Derived.RationalUp.pairMul_left_classifier_congr
        ⟨xUnary, unary_empty⟩ unitClassified
    have unitRight :
        IntPairClassifier
          (pairMul (x.val, BHist.Empty) (NatOne, BHist.Empty))
          (x.val, BHist.Empty) :=
      BEDC.Derived.RationalUp.pairMul_unit_right
        (x.val, BHist.Empty) ⟨xUnary, unary_empty⟩
    exact natModFn_of_nat_pair_classifier (M := M) (a := x.val)
      (IntPairClassifier_equivalence_fields.right.right.right.right.left
        mulClassified unitRight)
  have rawCongr :
      hsame (natModFn M raw.1)
        (natModFn M (BEDC.FKernel.Cont.append x.val raw.2)) :=
    pair_mod_nat_transport_of_component_mod MUnary MNonempty
      xUnary rawCarrier targetCarrier
      rawToTarget.left rawToTarget.right targetCongr
  exact crtPairResidue_of_pair_mod_congruence
    MUnary MNonempty xUnary rawCarrier x.isLt rawCongr

structure CRTEquiv (m n : BHist) where
  m_unary : UnaryHistory m
  n_unary : UnaryHistory n
  m_nonempty : hsame m BHist.Empty -> False
  n_nonempty : hsame n BHist.Empty -> False
  coprime : hsame (natGcdFn m n) NatOne
  forward : ZMod (crtModulus m n) -> ZMod m × ZMod n
  inverse : ZMod m × ZMod n -> ZMod (crtModulus m n)
  left_inverse :
    ∀ x : ZMod (crtModulus m n), zmodEq (inverse (forward x)) x
  right_inverse :
    ∀ pair : ZMod m × ZMod n,
      zmodEq (forward (inverse pair)).1 pair.1 ∧
        zmodEq (forward (inverse pair)).2 pair.2

def crtEquiv {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n)
    (mNonempty : hsame m BHist.Empty -> False)
    (nNonempty : hsame n BHist.Empty -> False)
    (coprime : hsame (natGcdFn m n) NatOne) :
    CRTEquiv m n where
  m_unary := mUnary
  n_unary := nUnary
  m_nonempty := mNonempty
  n_nonempty := nNonempty
  coprime := coprime
  forward := crtForward mUnary nUnary mNonempty nNonempty
  inverse := crtInverse mUnary nUnary mNonempty nNonempty
  left_inverse := crt_left_inv mUnary nUnary mNonempty nNonempty coprime
  right_inverse := crt_right_inv mUnary nUnary mNonempty nNonempty coprime

end BEDC.Derived.CRTUp
