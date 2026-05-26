import BEDC.Derived.DyadicLocatedCutUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicLocatedCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def dyadicLocatedCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicLocatedCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicLocatedCutEncodeBHist h

def dyadicLocatedCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicLocatedCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicLocatedCutDecodeBHist tail)

private theorem DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicLocatedCutFields : BEDC.Derived.DyadicLocatedCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.DyadicLocatedCutUp.mk L U G W R E H C P N =>
      [L, U, G, W, R, E, H, C, P, N]

def dyadicLocatedCutToEventFlow : BEDC.Derived.DyadicLocatedCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicLocatedCutFields x).map dyadicLocatedCutEncodeBHist

def dyadicLocatedCutFromEventFlow : EventFlow → Option BEDC.Derived.DyadicLocatedCutUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | gap :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (BEDC.Derived.DyadicLocatedCutUp.mk
                                                  (dyadicLocatedCutDecodeBHist lower)
                                                  (dyadicLocatedCutDecodeBHist upper)
                                                  (dyadicLocatedCutDecodeBHist gap)
                                                  (dyadicLocatedCutDecodeBHist window)
                                                  (dyadicLocatedCutDecodeBHist regular)
                                                  (dyadicLocatedCutDecodeBHist realSeal)
                                                  (dyadicLocatedCutDecodeBHist transport)
                                                  (dyadicLocatedCutDecodeBHist replay)
                                                  (dyadicLocatedCutDecodeBHist provenance)
                                                  (dyadicLocatedCutDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem DyadicLocatedCutTasteGate_single_carrier_alignment_round_trip
    (x : BEDC.Derived.DyadicLocatedCutUp) :
    dyadicLocatedCutFromEventFlow (dyadicLocatedCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U G W R E H C P N =>
      change
        some
          (BEDC.Derived.DyadicLocatedCutUp.mk
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist L))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist U))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist G))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist W))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist R))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist E))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist H))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist C))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist P))
            (dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist N))) =
          some (BEDC.Derived.DyadicLocatedCutUp.mk L U G W R E H C P N)
      rw [DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode L,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode U,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode G,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode W,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode R,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode E,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode H,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode C,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode P,
        DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode N]

private theorem dyadicLocatedCutToEventFlow_injective
    {x y : BEDC.Derived.DyadicLocatedCutUp} :
    dyadicLocatedCutToEventFlow x = dyadicLocatedCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicLocatedCutFromEventFlow (dyadicLocatedCutToEventFlow x) =
        dyadicLocatedCutFromEventFlow (dyadicLocatedCutToEventFlow y) :=
    congrArg dyadicLocatedCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicLocatedCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicLocatedCutTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicLocatedCutBHistCarrier :
    BHistCarrier BEDC.Derived.DyadicLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicLocatedCutToEventFlow
  fromEventFlow := dyadicLocatedCutFromEventFlow

instance dyadicLocatedCutChapterTasteGate :
    ChapterTasteGate BEDC.Derived.DyadicLocatedCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicLocatedCutFromEventFlow (dyadicLocatedCutToEventFlow x) = some x
    exact DyadicLocatedCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicLocatedCutToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.DyadicLocatedCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicLocatedCutChapterTasteGate

theorem DyadicLocatedCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicLocatedCutDecodeBHist (dyadicLocatedCutEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.DyadicLocatedCutUp,
        dyadicLocatedCutFromEventFlow (dyadicLocatedCutToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.DyadicLocatedCutUp,
          dyadicLocatedCutToEventFlow x = dyadicLocatedCutToEventFlow y → x = y) ∧
          dyadicLocatedCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DyadicLocatedCutTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DyadicLocatedCutTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact dyadicLocatedCutToEventFlow_injective heq
  · rfl

end BEDC.Derived.DyadicLocatedCutUp
