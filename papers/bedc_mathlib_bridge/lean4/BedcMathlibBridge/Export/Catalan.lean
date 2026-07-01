import BedcMathlibBridge.Constructive.Catalan

namespace BedcMathlibBridge.Export.Catalan

open BedcMathlibBridge.Constructive.Catalan

structure CatalanExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = bedcCatalan n
  central_binom_apply : ∀ n : Nat, readback n = Nat.centralBinom n / (n + 1)

def catalanExport : CatalanExportWitness where
  readback := bedcCatalan
  readback_apply := by
    intro n
    rfl
  central_binom_apply := bedcCatalan_eq_centralBinom_div

theorem catalan_eq_centralBinom_div (n : Nat) :
    BEDC.Derived.CatalanConvolutionUp.catalanBinomialDivision n =
      Nat.centralBinom n / (n + 1) :=
  BedcMathlibBridge.Constructive.Catalan.bedcCatalan_eq_centralBinom_div n

end BedcMathlibBridge.Export.Catalan
