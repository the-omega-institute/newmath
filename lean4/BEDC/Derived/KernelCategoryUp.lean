import BEDC.Derived.CategoryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.Derived.CategoryUp

def KernelCategoryCarrier
    (object hom identity composition associativity unit provenance name : BHist) : Prop :=
  UnaryHistory object ∧
    CategoryHomCarrier object object identity ∧
      Cont identity composition hom ∧
        hsame associativity (append hom composition) ∧
          hsame unit identity ∧
            hsame name (append provenance unit)

theorem KernelCategoryCarrier_identity_continuation
    {object hom identity composition associativity unit provenance name object' identity' : BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      hsame object object' →
      hsame identity identity' →
      CategoryHomCarrier object' object' identity' →
      Cont object' identity' object' := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier NameCert
  intro carrier sameObject sameIdentity transportedIdentity
  have baseIdentity : CategoryHomCarrier object object identity := carrier.right.left
  have movedIdentity : CategoryHomCarrier object' object' identity' :=
    CategoryHomCarrier_hsame_transport sameObject sameObject sameIdentity baseIdentity
  have sameDisplayed : hsame identity' BHist.Empty :=
    (CategoryHomCarrier_endomorphism_empty_iff.mp movedIdentity).right
  cases sameDisplayed
  exact cont_right_unit object'

end BEDC.Derived.KernelCategoryUp
