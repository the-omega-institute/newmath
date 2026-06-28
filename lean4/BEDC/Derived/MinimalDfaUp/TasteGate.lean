import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalDfaUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalDfaUp : Type where
  | packet
      (alphabet language congruence suffix distinguish states transition start accept automaton
        reach separate canonical transport replay provenance name : BHist) :
      MinimalDfaUp
  deriving DecidableEq

def MinimalDfaTasteGate_single_carrier_alignment_fields : MinimalDfaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalDfaUp.packet alphabet language congruence suffix distinguish states transition start
      accept automaton reach separate canonical transport replay provenance name =>
      [alphabet, language, congruence, suffix, distinguish, states, transition, start, accept,
        automaton, reach, separate, canonical, transport, replay, provenance, name]

def MinimalDfaTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MinimalDfaTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MinimalDfaTasteGate_single_carrier_alignment_encodeBHist h

def MinimalDfaTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MinimalDfaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
        (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def MinimalDfaTasteGate_single_carrier_alignment_toEventFlow :
    MinimalDfaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (MinimalDfaTasteGate_single_carrier_alignment_fields x).map
      MinimalDfaTasteGate_single_carrier_alignment_encodeBHist

def MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MinimalDfaUp
  -- BEDC touchpoint anchor: BHist BMark
  | [alphabet, language, congruence, suffix, distinguish, states, transition, start, accept,
      automaton, reach, separate, canonical, transport, replay, provenance, name] =>
      some
        (MinimalDfaUp.packet
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist alphabet)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist language)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist congruence)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist suffix)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist distinguish)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist states)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist transition)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist start)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist accept)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist automaton)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist reach)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist separate)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist canonical)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist transport)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist replay)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist provenance)
          (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

instance minimalDfaBHistCarrier : BHistCarrier MinimalDfaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MinimalDfaTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow

instance minimalDfaChapterTasteGate :
    ChapterTasteGate MinimalDfaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow
        (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow x) = some x
    cases x with
    | packet alphabet language congruence suffix distinguish states transition start accept
        automaton reach separate canonical transport replay provenance name =>
        change
          some
            (MinimalDfaUp.packet
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist alphabet))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist language))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist congruence))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist suffix))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist distinguish))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist states))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist transition))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist start))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist accept))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist automaton))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist reach))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist separate))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist canonical))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist transport))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist replay))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist provenance))
              (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist name))) =
            some
              (MinimalDfaUp.packet alphabet language congruence suffix distinguish states
                transition start accept automaton reach separate canonical transport replay
                provenance name)
        rw [MinimalDfaTasteGate_single_carrier_alignment_decode_encode alphabet,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode language,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode congruence,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode suffix,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode distinguish,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode states,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode transition,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode start,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode accept,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode automaton,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode reach,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode separate,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode canonical,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode transport,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode replay,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode provenance,
          MinimalDfaTasteGate_single_carrier_alignment_decode_encode name]
  layer_separation := by
    intro x y hxy heq
    have roundTrip :
        ∀ z : MinimalDfaUp,
          MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow
              (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow z) = some z := by
      intro z
      change
        MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow
          (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow z) = some z
      cases z with
      | packet alphabet language congruence suffix distinguish states transition start accept
          automaton reach separate canonical transport replay provenance name =>
          change
            some
              (MinimalDfaUp.packet
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist alphabet))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist language))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist congruence))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist suffix))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist distinguish))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist states))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist transition))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist start))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist accept))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist automaton))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist reach))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist separate))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist canonical))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist transport))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist replay))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist provenance))
                (MinimalDfaTasteGate_single_carrier_alignment_decodeBHist
                  (MinimalDfaTasteGate_single_carrier_alignment_encodeBHist name))) =
              some
                (MinimalDfaUp.packet alphabet language congruence suffix distinguish states
                  transition start accept automaton reach separate canonical transport replay
                  provenance name)
          rw [MinimalDfaTasteGate_single_carrier_alignment_decode_encode alphabet,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode language,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode congruence,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode suffix,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode distinguish,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode states,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode transition,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode start,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode accept,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode automaton,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode reach,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode separate,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode canonical,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode transport,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode replay,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode provenance,
            MinimalDfaTasteGate_single_carrier_alignment_decode_encode name]
    have hread :
        MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow
            (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow x) =
          MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow
            (MinimalDfaTasteGate_single_carrier_alignment_toEventFlow y) :=
      congrArg MinimalDfaTasteGate_single_carrier_alignment_fromEventFlow heq
    exact hxy (Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y))))

instance minimalDfaNontrivial : Nontrivial MinimalDfaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MinimalDfaUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MinimalDfaUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro samePacket
        cases samePacket⟩

theorem MinimalDfaTasteGate_single_carrier_alignment :
    (∀ alphabet language congruence suffix distinguish states transition start accept automaton
        reach separate canonical transport replay provenance name : BHist,
      MinimalDfaTasteGate_single_carrier_alignment_fields
          (MinimalDfaUp.packet alphabet language congruence suffix distinguish states transition
            start accept automaton reach separate canonical transport replay provenance name) =
        [alphabet, language, congruence, suffix, distinguish, states, transition, start, accept,
          automaton, reach, separate, canonical, transport, replay, provenance, name]) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro alphabet language congruence suffix distinguish states transition start accept automaton
    reach separate canonical transport replay provenance name
  rfl

end BEDC.Derived.MinimalDfaUp.TasteGate
