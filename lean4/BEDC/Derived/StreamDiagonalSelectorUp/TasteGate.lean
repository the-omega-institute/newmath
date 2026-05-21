import BEDC.Derived.StreamDiagonalSelectorUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StreamDiagonalSelectorUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StreamDiagonalSelectorUp : Type where
  | mk
      (schedule selector window readback dyadicLedger diagonalPacket routes provenance
        nameCert : BHist) : StreamDiagonalSelectorUp
  deriving DecidableEq

def streamDiagonalSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: streamDiagonalSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: streamDiagonalSelectorEncodeBHist h

def streamDiagonalSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (streamDiagonalSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (streamDiagonalSelectorDecodeBHist tail)

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def streamDiagonalSelectorFields : StreamDiagonalSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger diagonalPacket
      routes provenance nameCert =>
      [schedule, selector, window, readback, dyadicLedger, diagonalPacket, routes, provenance,
        nameCert]

def streamDiagonalSelectorToEventFlow : StreamDiagonalSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger diagonalPacket
      routes provenance nameCert =>
      [streamDiagonalSelectorEncodeBHist schedule,
        streamDiagonalSelectorEncodeBHist selector,
        streamDiagonalSelectorEncodeBHist window,
        streamDiagonalSelectorEncodeBHist readback,
        streamDiagonalSelectorEncodeBHist dyadicLedger,
        streamDiagonalSelectorEncodeBHist diagonalPacket,
        streamDiagonalSelectorEncodeBHist routes,
        streamDiagonalSelectorEncodeBHist provenance,
        streamDiagonalSelectorEncodeBHist nameCert]

def streamDiagonalSelectorFromEventFlow : EventFlow → Option StreamDiagonalSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | schedule :: rest0 =>
      match rest0 with
      | [] => none
      | selector :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagonalPacket :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routes :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (StreamDiagonalSelectorUp.mk
                                              (streamDiagonalSelectorDecodeBHist schedule)
                                              (streamDiagonalSelectorDecodeBHist selector)
                                              (streamDiagonalSelectorDecodeBHist window)
                                              (streamDiagonalSelectorDecodeBHist readback)
                                              (streamDiagonalSelectorDecodeBHist dyadicLedger)
                                              (streamDiagonalSelectorDecodeBHist diagonalPacket)
                                              (streamDiagonalSelectorDecodeBHist routes)
                                              (streamDiagonalSelectorDecodeBHist provenance)
                                              (streamDiagonalSelectorDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem streamDiagonalSelector_mk_congr
    {schedule schedule' selector selector' window window' readback readback'
      dyadicLedger dyadicLedger' diagonalPacket diagonalPacket' routes routes'
      provenance provenance' nameCert nameCert' : BHist}
    (hschedule : schedule' = schedule) (hselector : selector' = selector)
    (hwindow : window' = window) (hreadback : readback' = readback)
    (hdyadicLedger : dyadicLedger' = dyadicLedger)
    (hdiagonalPacket : diagonalPacket' = diagonalPacket) (hroutes : routes' = routes)
    (hprovenance : provenance' = provenance) (hnameCert : nameCert' = nameCert) :
    StreamDiagonalSelectorUp.mk schedule' selector' window' readback' dyadicLedger'
        diagonalPacket' routes' provenance' nameCert' =
      StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger diagonalPacket
        routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hschedule
  cases hselector
  cases hwindow
  cases hreadback
  cases hdyadicLedger
  cases hdiagonalPacket
  cases hroutes
  cases hprovenance
  cases hnameCert
  rfl

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip
    (x : StreamDiagonalSelectorUp) :
    streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert =>
      change
        some
            (StreamDiagonalSelectorUp.mk
              (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist schedule))
              (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist selector))
              (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist window))
              (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist readback))
              (streamDiagonalSelectorDecodeBHist
                (streamDiagonalSelectorEncodeBHist dyadicLedger))
              (streamDiagonalSelectorDecodeBHist
                (streamDiagonalSelectorEncodeBHist diagonalPacket))
              (streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist routes))
              (streamDiagonalSelectorDecodeBHist
                (streamDiagonalSelectorEncodeBHist provenance))
              (streamDiagonalSelectorDecodeBHist
                (streamDiagonalSelectorEncodeBHist nameCert))) =
          some
            (StreamDiagonalSelectorUp.mk schedule selector window readback dyadicLedger
              diagonalPacket routes provenance nameCert)
      exact
        congrArg some
          (streamDiagonalSelector_mk_congr
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode schedule)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode selector)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode window)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode readback)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode dyadicLedger)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode
              diagonalPacket)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode routes)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode provenance)
            (StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode nameCert))

private theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StreamDiagonalSelectorUp} :
    streamDiagonalSelectorToEventFlow x = streamDiagonalSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) =
        streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow y) :=
    congrArg streamDiagonalSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem streamDiagonalSelector_field_faithful :
    ∀ x y : StreamDiagonalSelectorUp,
      streamDiagonalSelectorFields x = streamDiagonalSelectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk schedule selector window readback dyadicLedger diagonalPacket routes provenance nameCert =>
      cases y with
      | mk schedule' selector' window' readback' dyadicLedger' diagonalPacket' routes'
          provenance' nameCert' =>
          cases hfields
          rfl

instance StreamDiagonalSelectorTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := streamDiagonalSelectorToEventFlow
  fromEventFlow := streamDiagonalSelectorFromEventFlow

instance StreamDiagonalSelectorTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x
    exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StreamDiagonalSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance streamDiagonalSelectorFieldFaithful : FieldFaithful StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := streamDiagonalSelectorFields
  field_faithful := streamDiagonalSelector_field_faithful

instance streamDiagonalSelectorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial StreamDiagonalSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StreamDiagonalSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StreamDiagonalSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def StreamDiagonalSelectorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate StreamDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StreamDiagonalSelectorTasteGate_single_carrier_alignment_ChapterTasteGate

def taste_gate : ChapterTasteGate StreamDiagonalSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  StreamDiagonalSelectorTasteGate_single_carrier_alignment_taste_gate

theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate StreamDiagonalSelectorUp) ∧
      Nonempty (FieldFaithful StreamDiagonalSelectorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial StreamDiagonalSelectorUp) ∧
      (∀ h : BHist,
        streamDiagonalSelectorDecodeBHist (streamDiagonalSelectorEncodeBHist h) = h) ∧
      (∀ x : StreamDiagonalSelectorUp,
        streamDiagonalSelectorFromEventFlow (streamDiagonalSelectorToEventFlow x) = some x) ∧
      (∀ x y : StreamDiagonalSelectorUp,
        streamDiagonalSelectorFields x = streamDiagonalSelectorFields y → x = y) ∧
      streamDiagonalSelectorEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      streamDiagonalSelectorEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨StreamDiagonalSelectorTasteGate_single_carrier_alignment_ChapterTasteGate⟩
  constructor
  · exact ⟨streamDiagonalSelectorFieldFaithful⟩
  constructor
  · exact ⟨streamDiagonalSelectorNontrivial⟩
  constructor
  · exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact StreamDiagonalSelectorTasteGate_single_carrier_alignment_round_trip
  constructor
  · exact streamDiagonalSelector_field_faithful
  constructor
  · rfl
  · rfl

end TasteGate

theorem StreamDiagonalSelectorTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.StreamDiagonalSelectorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.FieldFaithful TasteGate.StreamDiagonalSelectorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial TasteGate.StreamDiagonalSelectorUp) ∧
      (∀ h : BEDC.FKernel.Hist.BHist,
        TasteGate.streamDiagonalSelectorDecodeBHist
          (TasteGate.streamDiagonalSelectorEncodeBHist h) = h) ∧
      (∀ x : TasteGate.StreamDiagonalSelectorUp,
        TasteGate.streamDiagonalSelectorFromEventFlow
          (TasteGate.streamDiagonalSelectorToEventFlow x) = some x) ∧
      (∀ x y : TasteGate.StreamDiagonalSelectorUp,
        TasteGate.streamDiagonalSelectorFields x = TasteGate.streamDiagonalSelectorFields y →
          x = y) ∧
      TasteGate.streamDiagonalSelectorEncodeBHist BEDC.FKernel.Hist.BHist.Empty =
        ([] : BEDC.GroundCompiler.EventFlow.RawEvent) ∧
      TasteGate.streamDiagonalSelectorEncodeBHist
          (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) =
        [BEDC.FKernel.Mark.BMark.b1] := by
  exact TasteGate.StreamDiagonalSelectorTasteGate_single_carrier_alignment

end BEDC.Derived.StreamDiagonalSelectorUp
