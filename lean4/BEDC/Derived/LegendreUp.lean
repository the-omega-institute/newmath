import BEDC.Derived.ZModFieldUp
import BEDC.Derived.GcdUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.PadicUp.IntegerTower.RingCompletion

namespace BEDC.Derived.LegendreUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp

/-!
Legendre 数据以现有 `ZMod p` carrier 上的 kernel-checked 关系导出。
负号分支刻意保持为谓词分支：完整构造需要有限域平方类分解，
当前 BEDC kernel surface 尚未提供这一层结构。
-/

def zmodSquare {p : BHist} (prime : NatPrime p) (x : ZMod p) : ZMod p :=
  zmodMul p prime.left (NatPrime_empty_absurd prime) x x

def IsQR {p : BHist} (prime : NatPrime p) (a : ZMod p) : Prop :=
  ∃ x : ZMod p, zmodEq (zmodSquare prime x) a

def legendreZero : BEDC.Algebra.Rel.IntegerUp :=
  BEDC.Algebra.Rel.intZero

def legendreOne : BEDC.Algebra.Rel.IntegerUp :=
  BEDC.Algebra.Rel.intOne

def legendreNegOne : BEDC.Algebra.Rel.IntegerUp :=
  BEDC.Algebra.Rel.IntNeg BEDC.Algebra.Rel.intOne

def LegendreNonresidue {p : BHist} (prime : NatPrime p) (a : ZMod p) : Prop :=
  zmodNonzero a ∧ (IsQR prime a -> False)

def LegendreClassifies {p : BHist} (prime : NatPrime p) (a : ZMod p)
    (s : BEDC.Algebra.Rel.IntegerUp) : Prop :=
  (zmodEq a (zmodZero p prime.left (NatPrime_empty_absurd prime)) ∧
      BEDC.Algebra.Rel.IntEq s legendreZero) ∨
    (IsQR prime a ∧ zmodNonzero a ∧
      BEDC.Algebra.Rel.IntEq s legendreOne) ∨
      (LegendreNonresidue prime a ∧
        BEDC.Algebra.Rel.IntEq s legendreNegOne)

def legendreSym {p : BHist} (prime : NatPrime p) (a : ZMod p)
    (s : BEDC.Algebra.Rel.IntegerUp) : Prop :=
  LegendreClassifies prime a s

theorem zmodSquare_respects {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    zmodEq x y -> zmodEq (zmodSquare prime x) (zmodSquare prime y) := by
  intro same
  exact zmodMul_congr prime.left (NatPrime_empty_absurd prime) same same

theorem IsQR_respects {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    zmodEq a b -> IsQR prime a -> IsQR prime b := by
  intro same qr
  cases qr with
  | intro x hx =>
      exact ⟨x, zmodEq_trans hx same⟩

theorem zmodMul_zero_right {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime) x
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
  have xUnary : BEDC.FKernel.Unary.UnaryHistory x.val :=
    zmodVal_unary prime.left x
  have productZero :
      hsame (natMulFn x.val BHist.Empty) BHist.Empty :=
    NatMul_functional xUnary
      (natMulFn_rel xUnary unary_empty)
      (NatMul.zero xUnary)
  exact BEDC.Derived.PadicUp.natModFn_hsame_arg_transport
    (M := p) productZero

theorem zmodMul_zero_left {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) x)
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
  exact zmodEq_trans
    (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) x)
    (zmodMul_zero_right prime x)

theorem IsQR_zero {p : BHist} (prime : NatPrime p) :
    IsQR prime (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
  exact ⟨zmodZero p prime.left (NatPrime_empty_absurd prime),
    zmodEq_trans
      (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (zmodEq_symm
        (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
          (zmodZero p prime.left (NatPrime_empty_absurd prime))))⟩

theorem IsQR_one {p : BHist} (prime : NatPrime p) :
    IsQR prime (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  exact ⟨zmodOne p prime.left (NatPrime_empty_absurd prime),
    zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
      (zmodOne p prime.left (NatPrime_empty_absurd prime))⟩

theorem legendreSym_zero {p : BHist} (prime : NatPrime p) :
    legendreSym prime
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) legendreZero := by
  exact Or.inl ⟨zmodEq_refl _, BEDC.Derived.RationalUp.IntEq_refl _⟩

theorem legendreSym_one {p : BHist} (prime : NatPrime p) :
    legendreSym prime
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) legendreOne := by
  exact Or.inr (Or.inl
    ⟨IsQR_one prime, zmodOne_nonzero prime,
      BEDC.Derived.RationalUp.IntEq_refl _⟩)

theorem legendreSym_nonresidue {p : BHist} (prime : NatPrime p)
    {a : ZMod p} :
    LegendreNonresidue prime a -> legendreSym prime a legendreNegOne := by
  intro nonresidue
  exact Or.inr (Or.inr
    ⟨nonresidue, BEDC.Derived.RationalUp.IntEq_refl _⟩)

theorem zmodMul_nonzero {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    zmodNonzero a -> zmodNonzero b ->
      zmodNonzero
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a b) := by
  intro aNonzero bNonzero productZero
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  let zero := zmodZero p prime.left (NatPrime_empty_absurd prime)
  have productEqZero : zmodEq (mul a b) zero := productZero
  have leftTimesProductZero :
      zmodEq (mul (zmodInv prime a aNonzero) (mul a b)) zero :=
    zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodEq_refl (zmodInv prime a aNonzero)) productEqZero)
      (zmodMul_zero_right prime (zmodInv prime a aNonzero))
  have leftTimesProductIsB :
      zmodEq (mul (zmodInv prime a aNonzero) (mul a b)) b :=
    zmodEq_trans
      (zmodEq_symm
        (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
          (zmodInv prime a aNonzero) a b))
      (zmodEq_trans
        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
          (zmodMul_inv prime a aNonzero) (zmodEq_refl b))
        (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime) b))
  have bZero : zmodEq b zero :=
    zmodEq_trans (zmodEq_symm leftTimesProductIsB) leftTimesProductZero
  exact bNonzero bZero

theorem legendreSym_mul_zero_left {p : BHist} (prime : NatPrime p)
    (b : ZMod p) :
    legendreSym prime
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) b)
      (BEDC.Algebra.Rel.IntMul legendreZero legendreOne) := by
  have productZero :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodZero p prime.left (NatPrime_empty_absurd prime)) b)
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
    zmodMul_zero_left prime b
  exact Or.inl
    ⟨productZero,
      BEDC.Derived.RationalUp.IntEq_symm
        (BEDC.Derived.RationalUp.IntMul_zero legendreOne)⟩

theorem legendreSym_mul_zero_right {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    legendreSym prime
      (zmodMul p prime.left (NatPrime_empty_absurd prime) a
        (zmodZero p prime.left (NatPrime_empty_absurd prime)))
      (BEDC.Algebra.Rel.IntMul legendreOne legendreZero) := by
  have productZero :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a
          (zmodZero p prime.left (NatPrime_empty_absurd prime)))
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
    zmodMul_zero_right prime a
  exact Or.inl
    ⟨productZero,
      BEDC.Derived.RationalUp.IntEq_symm
        (BEDC.Derived.RationalUp.IntMul_one_left legendreZero)⟩

theorem zmodSquare_mul {p : BHist} (prime : NatPrime p)
    (x y : ZMod p) :
    zmodEq
      (zmodSquare prime
        (zmodMul p prime.left (NatPrime_empty_absurd prime) x y))
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodSquare prime x) (zmodSquare prime y)) := by
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  have assoc1 :
      zmodEq (mul (mul (mul x y) x) y)
        (mul (mul x y) (mul x y)) := by
    exact zmodMul_assoc prime.left (NatPrime_empty_absurd prime) (mul x y) x y
  have swapMiddle :
      zmodEq (mul (mul (mul x y) x) y)
        (mul (mul (mul x x) y) y) := by
    have leftAssoc :
        zmodEq (mul (mul x y) x) (mul x (mul y x)) :=
      zmodMul_assoc prime.left (NatPrime_empty_absurd prime) x y x
    have commuteYX : zmodEq (mul y x) (mul x y) :=
      zmodMul_comm prime.left (NatPrime_empty_absurd prime) y x
    have replace :
        zmodEq (mul x (mul y x)) (mul x (mul x y)) :=
      zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodEq_refl x) commuteYX
    have rightAssoc :
        zmodEq (mul x (mul x y)) (mul (mul x x) y) :=
      zmodEq_symm
        (zmodMul_assoc prime.left (NatPrime_empty_absurd prime) x x y)
    exact zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (zmodEq_trans leftAssoc (zmodEq_trans replace rightAssoc))
      (zmodEq_refl y)
  have assoc2 :
      zmodEq (mul (mul (mul x x) y) y)
        (mul (mul x x) (mul y y)) :=
    zmodMul_assoc prime.left (NatPrime_empty_absurd prime) (mul x x) y y
  exact zmodEq_trans (zmodEq_symm assoc1) (zmodEq_trans swapMiddle assoc2)

theorem IsQR_mul {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    IsQR prime a -> IsQR prime b ->
      IsQR prime (zmodMul p prime.left (NatPrime_empty_absurd prime) a b) := by
  intro qa qb
  cases qa with
  | intro x hx =>
      cases qb with
      | intro y hy =>
          exact ⟨zmodMul p prime.left (NatPrime_empty_absurd prime) x y,
            zmodEq_trans
              (zmodSquare_mul prime x y)
              (zmodMul_congr prime.left (NatPrime_empty_absurd prime) hx hy)⟩

theorem legendreSym_mul_qr {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    IsQR prime a -> zmodNonzero a ->
      IsQR prime b -> zmodNonzero b ->
        legendreSym prime a legendreOne ->
          legendreSym prime b legendreOne ->
            legendreSym prime
              (zmodMul p prime.left (NatPrime_empty_absurd prime) a b)
              (BEDC.Algebra.Rel.IntMul legendreOne legendreOne) := by
  intro qa aNonzero qb bNonzero _legA _legB
  have productQR : IsQR prime
      (zmodMul p prime.left (NatPrime_empty_absurd prime) a b) :=
    IsQR_mul prime qa qb
  have productNonzero : zmodNonzero
      (zmodMul p prime.left (NatPrime_empty_absurd prime) a b) := by
    exact zmodMul_nonzero prime aNonzero bNonzero
  change legendreSym prime
    (zmodMul p prime.left (NatPrime_empty_absurd prime) a b)
    (BEDC.Algebra.Rel.IntMul legendreOne legendreOne)
  exact Or.inr (Or.inl
    ⟨productQR, productNonzero,
      BEDC.Derived.RationalUp.IntEq_symm
        (BEDC.Derived.RationalUp.IntMul_one legendreOne)⟩)

theorem legendreSym_mul_qr_nonresidue {p : BHist} (prime : NatPrime p)
    {a b : ZMod p} :
    IsQR prime a -> zmodNonzero a ->
      LegendreNonresidue prime b ->
        legendreSym prime a legendreOne ->
          legendreSym prime b legendreNegOne ->
            legendreSym prime
              (zmodMul p prime.left (NatPrime_empty_absurd prime) a b)
              (BEDC.Algebra.Rel.IntMul legendreOne legendreNegOne) := by
  intro qa aNonzero nb _legA _legB
  let mul := zmodMul p prime.left (NatPrime_empty_absurd prime)
  have productNonzero : zmodNonzero (mul a b) :=
    zmodMul_nonzero prime aNonzero nb.left
  have productNotQR : IsQR prime (mul a b) -> False := by
    intro qProduct
    cases qa with
    | intro x hx =>
        cases qProduct with
        | intro z hz =>
            let invX := zmodInv prime x ?xNonzero
            have productToB :
                zmodEq (zmodSquare prime (mul z invX)) b := by
              have squareProduct :
                  zmodEq (zmodSquare prime (mul z invX))
                    (mul (zmodSquare prime z) (zmodSquare prime invX)) :=
                zmodSquare_mul prime z invX
              have invSquareProduct :
                  zmodEq (mul (zmodSquare prime z) (zmodSquare prime invX))
                    (mul (mul a b) (zmodSquare prime invX)) :=
                zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                  hz (zmodEq_refl (zmodSquare prime invX))
              have regroup :
                  zmodEq (mul (mul a b) (zmodSquare prime invX))
                    (mul b (mul a (zmodSquare prime invX))) := by
                exact zmodEq_trans
                  (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
                    a b (zmodSquare prime invX))
                  (zmodEq_trans
                    (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                      (zmodEq_refl a)
                      (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
                        b (zmodSquare prime invX)))
                    (zmodEq_trans
                      (zmodEq_symm
                        (zmodMul_assoc prime.left (NatPrime_empty_absurd prime)
                          a (zmodSquare prime invX) b))
                      (zmodEq_trans
                        (zmodMul_comm prime.left (NatPrime_empty_absurd prime)
                          (mul a (zmodSquare prime invX)) b)
                        (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                          (zmodEq_refl b)
                          (zmodEq_refl (mul a (zmodSquare prime invX)))))))
              have aInvSquareOne :
                  zmodEq (mul a (zmodSquare prime invX))
                    (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
                have replaceA :
                    zmodEq (mul a (zmodSquare prime invX))
                      (mul (zmodSquare prime x) (zmodSquare prime invX)) :=
                  zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                    (zmodEq_symm hx) (zmodEq_refl (zmodSquare prime invX))
                have squareInverse :
                    zmodEq (mul (zmodSquare prime x) (zmodSquare prime invX))
                      (zmodSquare prime (mul x invX)) :=
                  zmodEq_symm (zmodSquare_mul prime x invX)
                have invProductOne :
                    zmodEq (zmodSquare prime (mul x invX))
                      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
                  exact zmodEq_trans
                    (zmodSquare_respects prime
                      (zmodInv_mul prime x ?xNonzero))
                    (zmodOne_mul_left prime.left (NatPrime_empty_absurd prime)
                      (zmodOne p prime.left (NatPrime_empty_absurd prime)))
                exact zmodEq_trans replaceA
                  (zmodEq_trans squareInverse invProductOne)
              exact zmodEq_trans squareProduct
                (zmodEq_trans invSquareProduct
                  (zmodEq_trans regroup
                    (zmodEq_trans
                      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
                        (zmodEq_refl b) aInvSquareOne)
                      (zmodOne_mul_right prime.left
                        (NatPrime_empty_absurd prime) b))))
            exact nb.right ⟨mul z invX, productToB⟩
            · intro xZero
              have aZero : zmodEq a
                  (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
                zmodEq_trans
                  (zmodEq_symm hx)
                  (zmodEq_trans
                    (zmodSquare_respects prime
                      (show zmodEq x
                        (zmodZero p prime.left (NatPrime_empty_absurd prime)) from
                        xZero))
                    (zmodMul_zero_left prime
                      (zmodZero p prime.left (NatPrime_empty_absurd prime))))
              exact aNonzero aZero
  have productNonresidue : LegendreNonresidue prime (mul a b) :=
    ⟨productNonzero, productNotQR⟩
  change legendreSym prime (mul a b)
    (BEDC.Algebra.Rel.IntMul legendreOne legendreNegOne)
  exact Or.inr (Or.inr
    ⟨productNonresidue,
      BEDC.Derived.RationalUp.IntEq_symm
        (BEDC.Derived.RationalUp.IntMul_one legendreNegOne)⟩)

end BEDC.Derived.LegendreUp
