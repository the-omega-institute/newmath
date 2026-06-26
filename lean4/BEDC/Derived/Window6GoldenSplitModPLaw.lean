import BEDC.Derived.Window6ParryModPDescent

/-!
Window6 golden split mod-p law.

The golden minimum polynomial `x^2 - x - 1`, whose discriminant is `5`,
has its mod-p splitting predicate on the witness primes governed by
`p % 5 in {1,4}`.  This records the forward domination invariant behind
the Parry mod-p descent and links the Window6 transfer spectrum to the
Fibonacci entry-point arithmetic.

黄金最小多项式 `x^2 - x - 1` 的判别式为 `5`。在这里的 witness
素数窗口内，mod-p 分裂谓词由 `p % 5 in {1,4}` 支配；这是 Parry
mod-p descent 的 forward 支配不变量，并连接 Window6 转移谱与
Fibonacci entry-point 算术。
-/

namespace BEDC.Derived.Window6GoldenSplitModPLaw

def splitLawPrimes : List Nat :=
  [2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
   61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

theorem golden_split_law :
    splitLawPrimes.all
      (fun p =>
        BEDC.Derived.Window6ParryModPDescent.hasRootMod p ==
          (p % 5 == 1 || p % 5 == 4)) = true := by
  decide

theorem golden_inert_law :
    splitLawPrimes.all
      (fun p =>
        (BEDC.Derived.Window6ParryModPDescent.hasRootMod p == false) ==
          (p % 5 == 2 || p % 5 == 3)) = true := by
  decide

theorem golden_ramified_five :
    BEDC.Derived.Window6ParryModPDescent.rootsMod 5 = [3] := by
  decide

theorem golden_split_law_disc_five :
    BEDC.Derived.Window6ParryModPDescent.goldenDiscriminant = 5 ∧
      splitLawPrimes.all
        (fun p =>
          BEDC.Derived.Window6ParryModPDescent.hasRootMod p ==
            (p % 5 == 1 || p % 5 == 4)) = true := by
  exact ⟨BEDC.Derived.Window6ParryModPDescent.golden_minpoly_disc_five, golden_split_law⟩

end BEDC.Derived.Window6GoldenSplitModPLaw
