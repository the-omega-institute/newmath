import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBracketingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBracketingUp : Type where
  | mk :
      (lower upper gap stream readback realSeal locatedInterval transport continuation provenance
        name : BHist) →
        DyadicBracketingUp
  deriving DecidableEq

def dyadicBracketingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBracketingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBracketingEncodeBHist h

def dyadicBracketingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBracketingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBracketingDecodeBHist tail)

private theorem DyadicBracketingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicBracketingFields : DyadicBracketingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBracketingUp.mk lower upper gap stream readback realSeal locatedInterval transport
      continuation provenance name =>
      [lower, upper, gap, stream, readback, realSeal, locatedInterval, transport, continuation,
        provenance, name]

def dyadicBracketingToEventFlow : DyadicBracketingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicBracketingFields x).map dyadicBracketingEncodeBHist

def dyadicBracketingFromEventFlow : EventFlow → Option DyadicBracketingUp
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
              | stream :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | locatedInterval :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | continuation :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (DyadicBracketingUp.mk
                                                      (dyadicBracketingDecodeBHist lower)
                                                      (dyadicBracketingDecodeBHist upper)
                                                      (dyadicBracketingDecodeBHist gap)
                                                      (dyadicBracketingDecodeBHist stream)
                                                      (dyadicBracketingDecodeBHist readback)
                                                      (dyadicBracketingDecodeBHist realSeal)
                                                      (dyadicBracketingDecodeBHist
                                                        locatedInterval)
                                                      (dyadicBracketingDecodeBHist transport)
                                                      (dyadicBracketingDecodeBHist continuation)
                                                      (dyadicBracketingDecodeBHist provenance)
                                                      (dyadicBracketingDecodeBHist name))
                                              | _ :: _ => none

private theorem DyadicBracketingTasteGate_single_carrier_alignment_round_trip
    (x : DyadicBracketingUp) :
    dyadicBracketingFromEventFlow (dyadicBracketingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk lower upper gap stream readback realSeal locatedInterval transport continuation provenance
      name =>
      change
        some
          (DyadicBracketingUp.mk
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist lower))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist upper))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist gap))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist stream))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist readback))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist realSeal))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist locatedInterval))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist transport))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist continuation))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist provenance))
            (dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist name))) =
          some
            (DyadicBracketingUp.mk lower upper gap stream readback realSeal locatedInterval
              transport continuation provenance name)
      rw [DyadicBracketingTasteGate_single_carrier_alignment_decode_encode lower,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode upper,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode gap,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode stream,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode readback,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode realSeal,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode locatedInterval,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode transport,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode continuation,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode provenance,
        DyadicBracketingTasteGate_single_carrier_alignment_decode_encode name]

private theorem DyadicBracketingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicBracketingUp} :
    dyadicBracketingToEventFlow x = dyadicBracketingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBracketingFromEventFlow (dyadicBracketingToEventFlow x) =
        dyadicBracketingFromEventFlow (dyadicBracketingToEventFlow y) :=
    congrArg dyadicBracketingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicBracketingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicBracketingTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicBracketingBHistCarrier : BHistCarrier DyadicBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBracketingToEventFlow
  fromEventFlow := dyadicBracketingFromEventFlow

instance dyadicBracketingChapterTasteGate :
    ChapterTasteGate DyadicBracketingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicBracketingFromEventFlow (dyadicBracketingToEventFlow x) = some x
    exact DyadicBracketingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicBracketingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicBracketingTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicBracketingDecodeBHist (dyadicBracketingEncodeBHist h) = h) ∧
      (∀ x : DyadicBracketingUp,
        dyadicBracketingFromEventFlow (dyadicBracketingToEventFlow x) = some x) ∧
        (∀ x y : DyadicBracketingUp,
          dyadicBracketingToEventFlow x = dyadicBracketingToEventFlow y → x = y) ∧
          dyadicBracketingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact DyadicBracketingTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact DyadicBracketingTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DyadicBracketingTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicBracketingUp
