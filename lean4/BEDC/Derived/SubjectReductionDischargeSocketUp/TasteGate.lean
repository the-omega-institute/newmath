import BEDC.Derived.SubjectReductionDischargeSocketUp

namespace BEDC.Derived.SubjectReductionDischargeSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

theorem SubjectReductionDischargeSocketTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SubjectReductionDischargeSocketUp) ∧
      Nonempty (ChapterTasteGate SubjectReductionDischargeSocketUp) ∧
        (∀ h : BHist,
          subjectReductionDischargeSocketDecodeBHist
              (subjectReductionDischargeSocketEncodeBHist h) =
            h) ∧
          subjectReductionDischargeSocketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨subjectReductionDischargeSocketBHistCarrier⟩,
      ⟨subjectReductionDischargeSocketChapterTasteGate⟩,
      (by
        intro h
        induction h with
        | Empty => rfl
        | e0 h ih => exact congrArg BHist.e0 ih
        | e1 h ih => exact congrArg BHist.e1 ih),
      rfl⟩

end BEDC.Derived.SubjectReductionDischargeSocketUp
