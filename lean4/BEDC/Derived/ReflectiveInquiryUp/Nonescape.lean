import BEDC.Derived.ReflectiveInquiryUp.TasteGate

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ReflectiveInquiryUp_nonescape
    {physical formal signature classifier package transport ledger replay continuation
      openContinuation localName exported : BHist} :
    Cont continuation openContinuation exported -> hsame exported localName ->
      reflectiveInquiryToEventFlow
          (ReflectiveInquiryUp.mk physical formal signature classifier package transport ledger
            replay continuation openContinuation localName) =
        [reflectiveInquiryEncodeBHist physical, reflectiveInquiryEncodeBHist formal,
          reflectiveInquiryEncodeBHist signature, reflectiveInquiryEncodeBHist classifier,
          reflectiveInquiryEncodeBHist package, reflectiveInquiryEncodeBHist transport,
          reflectiveInquiryEncodeBHist ledger, reflectiveInquiryEncodeBHist replay,
          reflectiveInquiryEncodeBHist continuation,
          reflectiveInquiryEncodeBHist openContinuation,
          reflectiveInquiryEncodeBHist localName] ∧
        Cont continuation openContinuation exported ∧ hsame exported localName := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro continuationRoute exportedSameLocal
  exact ⟨rfl, continuationRoute, exportedSameLocal⟩

end BEDC.Derived.ReflectiveInquiryUp
