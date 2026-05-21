import BEDC.Derived.ReflectiveInquiryUp.TasteGate

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def ReflectiveInquiryClassifier
    (P F S K A R L H C Q N P' F' S' K' A' R' L' H' C' Q' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame P P' ∧ hsame F F' ∧ hsame S S' ∧ hsame K K' ∧ hsame A A' ∧
    hsame R R' ∧ hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame Q Q' ∧
    hsame N N'

theorem ReflectiveInquiry_ledgered_role_correspondence
    {P F S K A R L H C Q N P' F' S' K' A' R' L' H' C' Q' N' bridge audit : BHist} :
    ReflectiveInquiryClassifier P F S K A R L H C Q N P' F' S' K' A' R' L' H'
        C' Q' N' →
      Cont H C bridge →
        Cont bridge L audit →
          hsame P P' ∧ hsame F F' ∧ hsame S S' ∧ hsame K K' ∧ hsame A A' ∧
            hsame R R' ∧ hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame Q Q' ∧
            hsame N N' ∧ Cont H C bridge ∧ Cont bridge L audit := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classifier ledgerContinuation auditContinuation
  obtain
    ⟨sameP, sameF, sameS, sameK, sameA, sameR, sameL, sameH, sameC, sameQ,
      sameN⟩ := classifier
  exact
    ⟨sameP, sameF, sameS, sameK, sameA, sameR, sameL, sameH, sameC, sameQ,
      sameN, ledgerContinuation, auditContinuation⟩

end BEDC.Derived.ReflectiveInquiryUp
