import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.CatalanConvolutionUp
import Mathlib.Data.Nat.Choose.Central

namespace BedcMathlibBridge.Constructive.Catalan

private def mathlibCentralBinomProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.centralBinom n = Nat.centralBinom n := fun _ => rfl
  ()

def bedcCatalan (n : Nat) : Nat :=
  let _ := mathlibCentralBinomProvenanceAnchor
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
  rw [← Nat.two_mul n]
  exact congrArg (fun x => x / (n + 1)) (Nat.centralBinom_eq_two_mul_choose n).symm

end BedcMathlibBridge.Constructive.Catalan
