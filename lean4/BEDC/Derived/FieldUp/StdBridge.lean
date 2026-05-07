import BEDC.Derived.FieldUp.ProductApartness

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem FieldUp_StdBridge {p q r : BHist} :
    Cont p q r ->
      (FieldApartZero r <-> FieldApartZero p ∨ FieldApartZero q) ∧
        SemanticNameCert FieldApartZero FieldApartZero FieldApartZero hsame := by
  intro continuation
  exact And.intro (FieldApartZero_continuation_endpoint_split_iff continuation)
    FieldApartZero_semanticNameCert

end BEDC.Derived.FieldUp
