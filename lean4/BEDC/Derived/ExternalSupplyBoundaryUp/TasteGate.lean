import BEDC.Derived.ExternalSupplyBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ExternalSupplyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
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

theorem ExternalSupplyBoundary_namecert_obligations {B R I A G Q H C P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        ∃ packet : ExternalSupplyBoundaryUp,
          packet = ExternalSupplyBoundaryUp.mk B R I A G Q H C P N ∧ hsame row N)
      (fun row : BHist =>
        externalSupplyBoundaryFromEventFlow
              (externalSupplyBoundaryToEventFlow
                (ExternalSupplyBoundaryUp.mk B R I A G Q H C P N)) =
            some (ExternalSupplyBoundaryUp.mk B R I A G Q H C P N) ∧
          hsame row N)
      (fun row : BHist =>
        hsame row N ∧ externalSupplyBoundaryEncodeBHist BHist.Empty = ([] : List BMark))
      hsame := by
  -- BEDC touchpoint anchor: BHist BMark NameCert SemanticNameCert hsame
  refine
    { core := ?core
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · refine
      { carrier_inhabited := ?carrier_inhabited
        equiv_refl := ?equiv_refl
        equiv_symm := ?equiv_symm
        equiv_trans := ?equiv_trans
        carrier_respects_equiv := ?carrier_respects_equiv }
    · exact
        Exists.intro N
          (Exists.intro (ExternalSupplyBoundaryUp.mk B R I A G Q H C P N)
            (And.intro rfl (hsame_refl N)))
    · intro h _source
      exact hsame_refl h
    · intro h k hhk
      exact hsame_symm hhk
    · intro h k r hhk hkr
      exact hsame_trans hhk hkr
    · intro h k hhk source
      cases source with
      | intro packet packetRows =>
          cases packetRows with
          | intro packetEq rowName =>
              exact
                Exists.intro packet
                  (And.intro packetEq (hsame_trans (hsame_symm hhk) rowName))
  · intro row source
    cases source with
    | intro _packet packetRows =>
        cases packetRows with
        | intro _packetEq rowName =>
            exact
              And.intro
                (ExternalSupplyBoundaryTasteGate_single_carrier_alignment.right.left
                  (ExternalSupplyBoundaryUp.mk B R I A G Q H C P N))
                rowName
  · intro row source
    cases source with
    | intro _packet packetRows =>
        cases packetRows with
        | intro _packetEq rowName =>
            exact And.intro rowName rfl

end BEDC.Derived.ExternalSupplyBoundaryUp
