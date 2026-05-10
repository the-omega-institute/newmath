import BEDC.Derived.FunctorUp.SemanticCertificate

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.CategoryUp

theorem FunctorUp_StdBridge {p a b f : BHist} :
    PrefixFunctorCarrier p ->
      CategoryHomCarrier a b f ->
        CategoryHomCarrier (append p a) (append p b) f ∧
          SemanticNameCert
            (fun h : BHist => PrefixFunctorCarrier h ∧ hsame h p)
            (fun h : BHist => PrefixFunctorCarrier h ∧ hsame h p)
            (fun h : BHist => PrefixFunctorCarrier h ∧ hsame h p)
            hsame := by
  intro prefixCarrier homCarrier
  exact And.intro
    (FunctorPrefixHomCarrier_preserves prefixCarrier.prefix_unary homCarrier)
    (PrefixFunctorCarrier_semanticNameCert prefixCarrier.prefix_unary)

end BEDC.Derived.FunctorUp
