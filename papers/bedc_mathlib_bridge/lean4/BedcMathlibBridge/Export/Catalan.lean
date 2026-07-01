import BedcMathlibBridge.Constructive.Catalan

namespace BedcMathlibBridge.Export.Catalan

open BedcMathlibBridge.Constructive.Catalan

structure CatalanExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = bedcCatalan n
  central_binom_apply : ∀ n : Nat, readback n = Nat.centralBinom n / (n + 1)
  mathlib_catalan_apply : ∀ n : Nat, readback n = catalan n

def catalanExport : CatalanExportWitness where
  readback := bedcCatalan
  readback_apply := by
    intro n
    rfl
  central_binom_apply := bedcCatalan_eq_centralBinom_div
  mathlib_catalan_apply := bedcCatalan_eq_mathlib_catalan

theorem catalan_eq_mathlib_catalan (n : Nat) :
    BEDC.Derived.CatalanConvolutionUp.catalanBinomialDivision n = catalan n :=
  BedcMathlibBridge.Constructive.Catalan.bedcCatalan_eq_mathlib_catalan n

end BedcMathlibBridge.Export.Catalan
