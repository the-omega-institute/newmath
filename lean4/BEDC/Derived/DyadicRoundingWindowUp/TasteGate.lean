import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicRoundingWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicRoundingWindowUp : Type where
  | mk
      (stream precision adjacent readback rational real transport route provenance
        localName : BHist) :
      DyadicRoundingWindowUp
  deriving DecidableEq

def dyadicRoundingWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicRoundingWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicRoundingWindowEncodeBHist h

def dyadicRoundingWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicRoundingWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicRoundingWindowDecodeBHist tail)

private theorem dyadicRoundingWindow_decode_encode_bhist :
    ∀ h : BHist,
      dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicRoundingWindowFields : DyadicRoundingWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicRoundingWindowUp.mk stream precision adjacent readback rational real transport route
      provenance localName =>
      [stream, precision, adjacent, readback, rational, real, transport, route, provenance,
        localName]

def dyadicRoundingWindowToEventFlow : DyadicRoundingWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicRoundingWindowFields x).map dyadicRoundingWindowEncodeBHist

def dyadicRoundingWindowFromEventFlow : EventFlow → Option DyadicRoundingWindowUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | stream :: rest0 =>
      match rest0 with
      | [] => none
      | precision :: rest1 =>
          match rest1 with
          | [] => none
          | adjacent :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | rational :: rest4 =>
                      match rest4 with
                      | [] => none
                      | real :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DyadicRoundingWindowUp.mk
                                                  (dyadicRoundingWindowDecodeBHist stream)
                                                  (dyadicRoundingWindowDecodeBHist precision)
                                                  (dyadicRoundingWindowDecodeBHist adjacent)
                                                  (dyadicRoundingWindowDecodeBHist readback)
                                                  (dyadicRoundingWindowDecodeBHist rational)
                                                  (dyadicRoundingWindowDecodeBHist real)
                                                  (dyadicRoundingWindowDecodeBHist transport)
                                                  (dyadicRoundingWindowDecodeBHist route)
                                                  (dyadicRoundingWindowDecodeBHist provenance)
                                                  (dyadicRoundingWindowDecodeBHist localName))
                                          | _ :: _ => none

private theorem dyadicRoundingWindow_round_trip :
    ∀ x : DyadicRoundingWindowUp,
      dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream precision adjacent readback rational real transport route provenance localName =>
      change
        some
          (DyadicRoundingWindowUp.mk
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist stream))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist precision))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist adjacent))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist readback))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist rational))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist real))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist transport))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist route))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist provenance))
            (dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist localName))) =
          some
            (DyadicRoundingWindowUp.mk stream precision adjacent readback rational real transport
              route provenance localName)
      rw [dyadicRoundingWindow_decode_encode_bhist stream,
        dyadicRoundingWindow_decode_encode_bhist precision,
        dyadicRoundingWindow_decode_encode_bhist adjacent,
        dyadicRoundingWindow_decode_encode_bhist readback,
        dyadicRoundingWindow_decode_encode_bhist rational,
        dyadicRoundingWindow_decode_encode_bhist real,
        dyadicRoundingWindow_decode_encode_bhist transport,
        dyadicRoundingWindow_decode_encode_bhist route,
        dyadicRoundingWindow_decode_encode_bhist provenance,
        dyadicRoundingWindow_decode_encode_bhist localName]

private theorem dyadicRoundingWindowToEventFlow_injective
    {x y : DyadicRoundingWindowUp} :
    dyadicRoundingWindowToEventFlow x = dyadicRoundingWindowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) =
        dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow y) :=
    congrArg dyadicRoundingWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicRoundingWindow_round_trip x).symm
      (Eq.trans hread (dyadicRoundingWindow_round_trip y)))

instance dyadicRoundingWindowBHistCarrier :
    BHistCarrier DyadicRoundingWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicRoundingWindowToEventFlow
  fromEventFlow := dyadicRoundingWindowFromEventFlow

instance dyadicRoundingWindowChapterTasteGate :
    ChapterTasteGate DyadicRoundingWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicRoundingWindowFromEventFlow (dyadicRoundingWindowToEventFlow x) =
        some x
    exact dyadicRoundingWindow_round_trip x
  layer_separation := by
    intro _x _y hxy heq
    exact hxy (dyadicRoundingWindowToEventFlow_injective heq)

theorem DyadicRoundingWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicRoundingWindowDecodeBHist (dyadicRoundingWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicRoundingWindowUp) ∧
        Nonempty (ChapterTasteGate DyadicRoundingWindowUp) ∧
          dyadicRoundingWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dyadicRoundingWindow_decode_encode_bhist,
      Nonempty.intro dyadicRoundingWindowBHistCarrier,
      Nonempty.intro dyadicRoundingWindowChapterTasteGate,
      rfl⟩

end BEDC.Derived.DyadicRoundingWindowUp
