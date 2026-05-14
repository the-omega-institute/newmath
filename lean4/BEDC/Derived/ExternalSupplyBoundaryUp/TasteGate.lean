import BEDC.Derived.ExternalSupplyBoundaryUp

namespace BEDC.Derived.ExternalSupplyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

instance externalSupplyBoundaryFieldFaithful : FieldFaithful ExternalSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ExternalSupplyBoundaryUp.mk boundaryName requestedSupply nonInternalization acceptedForm
        gapLedger gateQuestion transport continuation provenance localName =>
        [boundaryName, requestedSupply, nonInternalization, acceptedForm, gapLedger,
          gateQuestion, transport, continuation, provenance, localName]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk boundaryName1 requestedSupply1 nonInternalization1 acceptedForm1 gapLedger1
        gateQuestion1 transport1 continuation1 provenance1 localName1 =>
        cases y with
        | mk boundaryName2 requestedSupply2 nonInternalization2 acceptedForm2 gapLedger2
            gateQuestion2 transport2 continuation2 provenance2 localName2 =>
            injection h with hBoundaryName t1
            injection t1 with hRequestedSupply t2
            injection t2 with hNonInternalization t3
            injection t3 with hAcceptedForm t4
            injection t4 with hGapLedger t5
            injection t5 with hGateQuestion t6
            injection t6 with hTransport t7
            injection t7 with hContinuation t8
            injection t8 with hProvenance t9
            injection t9 with hLocalName _
            cases hBoundaryName
            cases hRequestedSupply
            cases hNonInternalization
            cases hAcceptedForm
            cases hGapLedger
            cases hGateQuestion
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

instance externalSupplyBoundaryNontrivial : Nontrivial ExternalSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.ExternalSupplyBoundaryUp
