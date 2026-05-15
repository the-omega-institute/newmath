import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

instance realCompletionSelectorSealFieldFaithful : FieldFaithful RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist FieldFaithful
  fields := fun x =>
    match x with
    | RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport continuation
        provenance name =>
        [budget, window, readback, limit, endpoint, transport, continuation, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk budget1 window1 readback1 limit1 endpoint1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk budget2 window2 readback2 limit2 endpoint2 transport2 continuation2 provenance2 name2 =>
            cases h
            rfl

instance realCompletionSelectorSealNontrivial : Nontrivial RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionSelectorSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionSelectorSealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.RealCompletionSelectorSealUp
