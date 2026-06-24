import BEDC.Derived.ZModUp
import BEDC.Derived.GcdUp

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

end BEDC.Derived.CRTUp
