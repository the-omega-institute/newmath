import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

instance realCompletionSelectorSealFieldFaithful : FieldFaithful RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist FieldFaithful
  fields := fun x =>
    match x with
    | RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport
        continuation provenance name =>
        [budget, window, readback, limit, endpoint, transport, continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk budget1 window1 readback1 limit1 endpoint1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk budget2 window2 readback2 limit2 endpoint2 transport2 continuation2 provenance2 name2 =>
            injection h with hBudget tail1
            injection tail1 with hWindow tail2
            injection tail2 with hReadback tail3
            injection tail3 with hLimit tail4
            injection tail4 with hEndpoint tail5
            injection tail5 with hTransport tail6
            injection tail6 with hContinuation tail7
            injection tail7 with hProvenance tail8
            injection tail8 with hName _
            cases hBudget
            cases hWindow
            cases hReadback
            cases hLimit
            cases hEndpoint
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

instance realCompletionSelectorSealNontrivial : Nontrivial RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionSelectorSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionSelectorSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.RealCompletionSelectorSealUp
