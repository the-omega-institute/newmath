import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_endpoint_transport_closure
    {object hom identity composition associativity unit provenance name object' identity' :
      BHist} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name →
      hsame object object' →
        hsame identity identity' →
          CategoryHomCarrier object' object' identity' ∧ Cont object' identity' object' ∧
            hsame associativity (append hom composition) ∧ hsame unit identity ∧
              hsame name (append provenance unit) := by
  -- BEDC touchpoint anchor: BHist hsame Cont CategoryHomCarrier
  intro carrier sameObject sameIdentity
  have carrierPacket :
      KernelCategoryCarrier object hom identity composition associativity unit provenance name :=
    carrier
  obtain ⟨_objectUnary, identityCarrier, _identityCompositionHom, associativitySame,
    unitSame, nameSame⟩ := carrier
  have transportedIdentity : CategoryHomCarrier object' object' identity' :=
    CategoryHomCarrier_hsame_transport sameObject sameObject sameIdentity identityCarrier
  have transportedContinuation : Cont object' identity' object' :=
    KernelCategoryCarrier_identity_continuation carrierPacket sameObject sameIdentity
      transportedIdentity
  exact
    ⟨transportedIdentity, transportedContinuation, associativitySame, unitSame, nameSame⟩

end BEDC.Derived.KernelCategoryUp
