import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionContinuationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionContinuationUp : Type where
  | mk :
      (request bindSource schedule window dyadic readback realSeal transport replay provenance
        localName : BHist) →
        CauchyCompletionContinuationUp
  deriving DecidableEq

def cauchyCompletionContinuationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionContinuationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionContinuationEncodeBHist h

def cauchyCompletionContinuationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionContinuationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionContinuationDecodeBHist tail)

private theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionContinuationDecodeBHist
        (cauchyCompletionContinuationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionContinuationFields : CauchyCompletionContinuationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionContinuationUp.mk request bindSource schedule window dyadic readback realSeal
      transport replay provenance localName =>
      [request, bindSource, schedule, window, dyadic, readback, realSeal, transport, replay,
        provenance, localName]

def cauchyCompletionContinuationToEventFlow : CauchyCompletionContinuationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionContinuationFields x).map cauchyCompletionContinuationEncodeBHist

def cauchyCompletionContinuationFromEventFlow :
    EventFlow → Option CauchyCompletionContinuationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | request :: rest0 =>
      match rest0 with
      | [] => none
      | bindSource :: rest1 =>
          match rest1 with
          | [] => none
          | schedule :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadic :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyCompletionContinuationUp.mk
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        request)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        bindSource)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        schedule)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        window)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        dyadic)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        readback)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        realSeal)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        transport)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        replay)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        provenance)
                                                      (cauchyCompletionContinuationDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionContinuationUp,
      cauchyCompletionContinuationFromEventFlow
        (cauchyCompletionContinuationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request bindSource schedule window dyadic readback realSeal transport replay provenance
      localName =>
      change
        some
          (CauchyCompletionContinuationUp.mk
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist request))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist bindSource))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist schedule))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist window))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist dyadic))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist readback))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist realSeal))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist transport))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist replay))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist provenance))
            (cauchyCompletionContinuationDecodeBHist
              (cauchyCompletionContinuationEncodeBHist localName))) =
          some
            (CauchyCompletionContinuationUp.mk request bindSource schedule window dyadic readback
              realSeal transport replay provenance localName)
      rw [CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode request,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode bindSource,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode schedule,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode window,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode dyadic,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode readback,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode realSeal,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode transport,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode replay,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode provenance,
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode localName]

private theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionContinuationUp} :
    cauchyCompletionContinuationToEventFlow x =
      cauchyCompletionContinuationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow x) =
        cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow y) :=
    congrArg cauchyCompletionContinuationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionContinuationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionContinuationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCompletionContinuationUp,
      cauchyCompletionContinuationFields x = cauchyCompletionContinuationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request₁ bindSource₁ schedule₁ window₁ dyadic₁ readback₁ realSeal₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk request₂ bindSource₂ schedule₂ window₂ dyadic₂ readback₂ realSeal₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection hfields with hRequest tail0
          injection tail0 with hBindSource tail1
          injection tail1 with hSchedule tail2
          injection tail2 with hWindow tail3
          injection tail3 with hDyadic tail4
          injection tail4 with hReadback tail5
          injection tail5 with hRealSeal tail6
          injection tail6 with hTransport tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hRequest
          subst hBindSource
          subst hSchedule
          subst hWindow
          subst hDyadic
          subst hReadback
          subst hRealSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance cauchyCompletionContinuationBHistCarrier :
    BHistCarrier CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionContinuationToEventFlow
  fromEventFlow := cauchyCompletionContinuationFromEventFlow

instance cauchyCompletionContinuationChapterTasteGate :
    ChapterTasteGate CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow x) = some x
    exact CauchyCompletionContinuationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionContinuationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCompletionContinuationFieldFaithful :
    FieldFaithful CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionContinuationFields
  field_faithful :=
    CauchyCompletionContinuationTasteGate_single_carrier_alignment_fields_faithful

instance cauchyCompletionContinuationNontrivial : Nontrivial CauchyCompletionContinuationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionContinuationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionContinuationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionContinuationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionContinuationChapterTasteGate

theorem CauchyCompletionContinuationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionContinuationDecodeBHist
        (cauchyCompletionContinuationEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionContinuationUp,
        cauchyCompletionContinuationFromEventFlow
          (cauchyCompletionContinuationToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionContinuationUp,
          cauchyCompletionContinuationToEventFlow x =
            cauchyCompletionContinuationToEventFlow y → x = y) ∧
          cauchyCompletionContinuationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionContinuationTasteGate_single_carrier_alignment_decode,
      CauchyCompletionContinuationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionContinuationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionContinuationUp
