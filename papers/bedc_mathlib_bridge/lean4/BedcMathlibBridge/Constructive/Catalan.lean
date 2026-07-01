import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.CatalanConvolutionUp
import Mathlib.Combinatorics.Enumerative.Catalan

namespace BedcMathlibBridge.Constructive.Catalan

abbrev bedcCatalan (n : Nat) : Nat :=
  BEDC.Derived.CatalanConvolutionUp.catalanBinomialDivision n

private theorem bedcChoose_eq_nat_choose (n k : Nat) :
    BEDC.Derived.CatalanConvolutionUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

theorem bedcCatalan_eq_centralBinom_div (n : Nat) :
    bedcCatalan n = Nat.centralBinom n / (n + 1) := by
  unfold bedcCatalan
  rw [BEDC.Derived.CatalanConvolutionUp.catalan_binomial_division_surface]
  rw [bedcChoose_eq_nat_choose]
  exact congrArg (fun x => x / (n + 1)) (Nat.centralBinom_eq_two_mul_choose n).symm

theorem bedcCatalan_eq_mathlib_catalan (n : Nat) :
    bedcCatalan n = catalan n := by
  rw [bedcCatalan_eq_centralBinom_div]
  exact (catalan_eq_centralBinom_div n).symm

end BedcMathlibBridge.Constructive.Catalan
