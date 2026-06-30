import BEDC.Derived.NonAxiomAdmissionUp.TasteGate

namespace BEDC.Derived.NonAxiomAdmissionUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem NonAxiomAdmissionCarrier_namecert_obligations :
    Nonempty (ChapterTasteGate NonAxiomAdmissionUp) ∧
      Nonempty (FieldFaithful NonAxiomAdmissionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial NonAxiomAdmissionUp) ∧
          (∀ x : NonAxiomAdmissionUp,
            ∃ X F W H C P N : BHist,
              x = NonAxiomAdmissionUp.mk X F W H C P N ∧
                FieldFaithful.fields x = [X, F, W, H, C, P, N]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨nonAxiomAdmissionChapterTasteGate⟩,
      ⟨nonAxiomAdmissionFieldFaithful⟩,
      ⟨nonAxiomAdmissionNontrivial⟩,
      by
        intro x
        cases x with
        | mk X F W H C P N =>
            exact ⟨X, F, W, H, C, P, N, rfl, rfl⟩⟩

end BEDC.Derived.NonAxiomAdmissionUp
