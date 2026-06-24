import BEDC.Derived.SheafificationUp.TasteGate

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate
open BEDC.Derived.SheafificationUp.TasteGate

theorem SheafificationSheafHandoff (x : SheafificationUp) :
    ∃ C T J P L G S H R Q N : BHist,
      x = SheafificationUp.mk C T J P L G S H R Q N ∧
        List.Mem (sheafificationEncodeBHist C) (BHistCarrier.toEventFlow x) ∧
          List.Mem (sheafificationEncodeBHist P) (BHistCarrier.toEventFlow x) ∧
            List.Mem (sheafificationEncodeBHist S) (BHistCarrier.toEventFlow x) ∧
              List.Mem BMark.b0 (sheafificationEncodeBHist (BHist.e0 BHist.Empty)) ∧
                hsame S S ∧ hsame L L ∧ hsame G G := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier hsame
  cases x with
  | mk C T J P L G S H R Q N =>
      exists C
      exists T
      exists J
      exists P
      exists L
      exists G
      exists S
      exists H
      exists R
      exists Q
      exists N
      constructor
      · rfl
      constructor
      · exact List.Mem.head _
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      constructor
      · exact
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
      constructor
      · exact List.Mem.head _
      · exact ⟨hsame_refl S, hsame_refl L, hsame_refl G⟩

end BEDC.Derived.SheafificationUp
