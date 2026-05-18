import BEDC.Derived.CofinalModulusSealUp.TasteGate

namespace BEDC.Derived.CofinalModulusSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Meta.TasteGate

theorem CofinalModulusSealUp_StdBridge
    (budget modulus window limit regSeq stream dyadic real transport replay provenance
      name : BHist) :
    Nonempty (ChapterTasteGate CofinalModulusSealUp) ∧
      cofinalModulusSealEncodeBHist BHist.Empty = ([] : List BMark) ∧
        BHistCarrier.fromEventFlow
            (BHistCarrier.toEventFlow
              (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
                transport replay provenance name)) =
          some
            (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
              transport replay provenance name) ∧
          hsame budget budget ∧ hsame modulus modulus ∧ hsame window window ∧
            hsame real real := by
  -- BEDC touchpoint anchor: BHist BMark hsame ChapterTasteGate
  constructor
  · exact ⟨cofinalModulusSealChapterTasteGate⟩
  · constructor
    · rfl
    · constructor
      · change
          BHistCarrier.fromEventFlow
              (BHistCarrier.toEventFlow
                (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
                  transport replay provenance name)) =
            some
              (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
                transport replay provenance name)
        exact
          ChapterTasteGate.round_trip
            (CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
              transport replay provenance name)
      · exact
          ⟨hsame_refl budget, hsame_refl modulus, hsame_refl window, hsame_refl real⟩

end BEDC.Derived.CofinalModulusSealUp
