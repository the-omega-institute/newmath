import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailControlUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailControlUp : Type where
  | mk :
      (request window dyadic threshold regular terminalSeal transport continuation provenance localNameCert :
        BHist) ->
        CauchyTailControlUp
  deriving DecidableEq

def cauchyTailControlEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailControlEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailControlEncodeBHist h

def cauchyTailControlDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailControlDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailControlDecodeBHist tail)

theorem CauchyTailControlTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailControlFields : CauchyTailControlUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailControlUp.mk request window dyadic threshold regular terminalSeal transport continuation
      provenance localNameCert =>
      [request, window, dyadic, threshold, regular, terminalSeal, transport, continuation, provenance,
        localNameCert]

def cauchyTailControlToEventFlow : CauchyTailControlUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailControlFields x).map cauchyTailControlEncodeBHist

def cauchyTailControlFromEventFlow : EventFlow -> Option CauchyTailControlUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | request :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | dyadic :: rest2 =>
              match rest2 with
              | [] => none
              | threshold :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | terminalSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localNameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyTailControlUp.mk
                                                  (cauchyTailControlDecodeBHist request)
                                                  (cauchyTailControlDecodeBHist window)
                                                  (cauchyTailControlDecodeBHist dyadic)
                                                  (cauchyTailControlDecodeBHist threshold)
                                                  (cauchyTailControlDecodeBHist regular)
                                                  (cauchyTailControlDecodeBHist terminalSeal)
                                                  (cauchyTailControlDecodeBHist transport)
                                                  (cauchyTailControlDecodeBHist continuation)
                                                  (cauchyTailControlDecodeBHist provenance)
                                                  (cauchyTailControlDecodeBHist localNameCert))
                                          | _ :: _ => none

theorem CauchyTailControlTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyTailControlUp,
      cauchyTailControlFromEventFlow (cauchyTailControlToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request window dyadic threshold regular terminalSeal transport continuation provenance
      localNameCert =>
      change
        some
          (CauchyTailControlUp.mk
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist request))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist window))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist dyadic))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist threshold))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist regular))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist terminalSeal))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist transport))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist continuation))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist provenance))
            (cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist localNameCert))) =
          some
            (CauchyTailControlUp.mk request window dyadic threshold regular terminalSeal transport
              continuation provenance localNameCert)
      rw [CauchyTailControlTasteGate_single_carrier_alignment_decode_encode request,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode window,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode dyadic,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode threshold,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode regular,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode terminalSeal,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode continuation,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyTailControlTasteGate_single_carrier_alignment_decode_encode localNameCert]

theorem CauchyTailControlTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailControlUp} :
    cauchyTailControlToEventFlow x = cauchyTailControlToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailControlFromEventFlow (cauchyTailControlToEventFlow x) =
        cauchyTailControlFromEventFlow (cauchyTailControlToEventFlow y) :=
    congrArg cauchyTailControlFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailControlTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailControlTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchyTailControlTasteGate_single_carrier_alignment_field_faithful :
    forall x y : CauchyTailControlUp,
      cauchyTailControlFields x = cauchyTailControlFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request₁ window₁ dyadic₁ threshold₁ regular₁ terminalSeal₁ transport₁ continuation₁
      provenance₁ localNameCert₁ =>
      cases y with
      | mk request₂ window₂ dyadic₂ threshold₂ regular₂ terminalSeal₂ transport₂ continuation₂
          provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance cauchyTailControlBHistCarrier : BHistCarrier CauchyTailControlUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailControlToEventFlow
  fromEventFlow := cauchyTailControlFromEventFlow

instance cauchyTailControlChapterTasteGate : ChapterTasteGate CauchyTailControlUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyTailControlTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailControlTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTailControlFieldFaithful : FieldFaithful CauchyTailControlUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailControlFields
  field_faithful := CauchyTailControlTasteGate_single_carrier_alignment_field_faithful

def cauchyTailControlTasteGate : ChapterTasteGate CauchyTailControlUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailControlChapterTasteGate

theorem CauchyTailControlTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailControlDecodeBHist (cauchyTailControlEncodeBHist h) = h) ∧
      (∀ x : CauchyTailControlUp,
        cauchyTailControlFromEventFlow (cauchyTailControlToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailControlUp,
          cauchyTailControlToEventFlow x = cauchyTailControlToEventFlow y → x = y) ∧
          cauchyTailControlEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyTailControlTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchyTailControlTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyTailControlTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyTailControlUp
