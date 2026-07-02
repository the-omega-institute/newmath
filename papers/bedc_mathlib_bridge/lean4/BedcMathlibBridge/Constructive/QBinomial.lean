import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.QBinomialUp
import Mathlib.Data.Nat.Choose.Basic

/-!
q-binomial (Gaussian binomial) structural correspondence.

`BEDC.Derived.QBinomialUp.qBinomial n k : List Nat` 是 q-二项式系数的多项式
表示 (`Poly := List Nat` 记录每个单项的指数). 这是一个**结构化**对象, 比标量
读回更丰富: 它是一个多项式, 不是一个自然数.

本模块桥接的是 q-analog 在 `q = 1` 处的特化: `polyEvalOne` 把多项式坍缩为其
系数之和 (一次 `List Nat -> Nat` 折叠), 而这个值恰好等于经典二项式系数. 于是有
结构保持等式

  `polyEvalOne (qBinomial n k) = Nat.choose n k`,

即 BEDC 的 Gaussian 二项多项式在 `q = 1` 处求值复现 mathlib 的经典 `Nat.choose`.
证明复用已核验的 `QBinomialUp.qBinomial_evalOne` (给出等于 `BinomialIdentitiesUp.C`)
与桥内 `Constructive.Binomial.bedcChoose_eq_nat_choose` (给出 `= Nat.choose`);
`BinomialIdentitiesUp.C` 与 `bedcChooseNat` 定义相等, 故中间步用 `change` 对齐.
-/

namespace BedcMathlibBridge.Constructive.QBinomial

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : ∀ n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

/-- q=1 evaluation of the BEDC q-binomial polynomial: a structural fold
`List Nat -> Nat` collapsing the Gaussian binomial to its coefficient sum. -/
def toNat (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.QBinomialUp.polyEvalOne (BEDC.Derived.QBinomialUp.qBinomial n k)

theorem toNat_eq_qBinomial_evalOne (n k : Nat) :
    toNat n k =
      BEDC.Derived.QBinomialUp.polyEvalOne
        (BEDC.Derived.QBinomialUp.qBinomial n k) :=
  rfl

/-- Boundary: the empty polynomial evaluates to `0`, matching
`Nat.choose 0 (k+1) = 0`. -/
theorem toNat_zero_succ (k : Nat) : toNat 0 (Nat.succ k) = 0 := by
  rfl

/-- Boundary: the constant polynomial evaluates to `1`, matching
`Nat.choose n 0 = 1`. -/
theorem toNat_zero_right (n : Nat) : toNat n 0 = 1 := by
  cases n <;> rfl

/-- Structure-preserving Pascal step transported through the q=1 evaluation:
`polyEvalOne` is additive over `polyAdd` and invariant under `qShift`, so the
Gaussian Pascal recurrence collapses to the ordinary additive recurrence. -/
theorem toNat_pascal (n k : Nat) :
    toNat (Nat.succ n) (Nat.succ k) = toNat n k + toNat n (Nat.succ k) := by
  change
    BEDC.Derived.QBinomialUp.polyEvalOne
        (BEDC.Derived.QBinomialUp.qBinomial (Nat.succ n) (Nat.succ k)) =
      BEDC.Derived.QBinomialUp.polyEvalOne
          (BEDC.Derived.QBinomialUp.qBinomial n k) +
        BEDC.Derived.QBinomialUp.polyEvalOne
          (BEDC.Derived.QBinomialUp.qBinomial n (Nat.succ k))
  rw [BEDC.Derived.QBinomialUp.qBinomial_pascal n k]
  rw [BEDC.Derived.QBinomialUp.polyEvalOne_append]
  rw [BEDC.Derived.QBinomialUp.polyEvalOne_qShift]

/-- The main structural correspondence: the BEDC Gaussian binomial polynomial,
evaluated at `q = 1`, equals mathlib's `Nat.choose`. -/
theorem toNat_eq_nat_choose (n k : Nat) : toNat n k = Nat.choose n k := by
  have hEval :
      BEDC.Derived.QBinomialUp.polyEvalOne
          (BEDC.Derived.QBinomialUp.qBinomial n k) =
        BEDC.Derived.BinomialIdentitiesUp.C n k :=
    BEDC.Derived.QBinomialUp.qBinomial_evalOne n k
  have hChoose :
      BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k := by
    change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
    exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k
  calc
    toNat n k =
        BEDC.Derived.QBinomialUp.polyEvalOne
          (BEDC.Derived.QBinomialUp.qBinomial n k) := rfl
    _ = BEDC.Derived.BinomialIdentitiesUp.C n k := hEval
    _ = Nat.choose n k := hChoose

end BedcMathlibBridge.Constructive.QBinomial
