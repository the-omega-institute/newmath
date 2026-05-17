import BEDC.Derived.CofinalModulusSealUp.TasteGate

namespace BEDC.Derived.CofinalModulusSealUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CofinalModulusSealRegSeqRatWindowFactorization
    (budget modulus window limit regSeq stream dyadic real transport replay provenance
      name : BHist) :
    ∃ x : CofinalModulusSealUp,
      x =
          CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real
            transport replay provenance name ∧
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
          BHistCarrier.toEventFlow x ≠
            BHistCarrier.toEventFlow
              (CofinalModulusSealUp.mk (BHist.e0 budget) modulus window limit regSeq stream
                dyadic real transport replay provenance name) := by
  -- BEDC touchpoint anchor: BHist BHistCarrier ChapterTasteGate
  let x :=
    CofinalModulusSealUp.mk budget modulus window limit regSeq stream dyadic real transport
      replay provenance name
  refine ⟨x, rfl, ?_, ?_⟩
  · exact ChapterTasteGate.round_trip x
  · intro heq
    have differentCarrier :
        x ≠
          CofinalModulusSealUp.mk (BHist.e0 budget) modulus window limit regSeq stream dyadic
            real transport replay provenance name := by
      intro sameCarrier
      dsimp [x] at sameCarrier
      injection sameCarrier with sameBudget
      exact hsame_extension_self_absurd.1 budget sameBudget.symm
    exact (ChapterTasteGate.layer_separation x _ differentCarrier) heq

end BEDC.Derived.CofinalModulusSealUp
