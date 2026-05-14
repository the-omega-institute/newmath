import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverAccumulationClockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverAccumulationClockUp : Type where
  | mk (present successor edge residue transport route provenance name : BHist) :
      ObserverAccumulationClockUp
  deriving DecidableEq

def observerAccumulationClockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerAccumulationClockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerAccumulationClockEncodeBHist h

def observerAccumulationClockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerAccumulationClockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerAccumulationClockDecodeBHist tail)

private theorem observerAccumulationClockDecode_encode_bhist :
    ∀ h : BHist,
      observerAccumulationClockDecodeBHist (observerAccumulationClockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerAccumulationClockToEventFlow : ObserverAccumulationClockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverAccumulationClockUp.mk present successor edge residue transport route provenance name =>
      [[BMark.b0],
        observerAccumulationClockEncodeBHist present,
        [BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist successor,
        [BMark.b1, BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist edge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerAccumulationClockEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerAccumulationClockEncodeBHist name]

private def observerAccumulationClockDecodePacket
    (present successor edge residue transport route provenance name : RawEvent) :
    ObserverAccumulationClockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ObserverAccumulationClockUp.mk
    (observerAccumulationClockDecodeBHist present)
    (observerAccumulationClockDecodeBHist successor)
    (observerAccumulationClockDecodeBHist edge)
    (observerAccumulationClockDecodeBHist residue)
    (observerAccumulationClockDecodeBHist transport)
    (observerAccumulationClockDecodeBHist route)
    (observerAccumulationClockDecodeBHist provenance)
    (observerAccumulationClockDecodeBHist name)

def observerAccumulationClockFromEventFlow : EventFlow → Option ObserverAccumulationClockUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | present :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | successor :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | edge :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | residue :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (observerAccumulationClockDecodePacket
                                                                          present successor
                                                                          edge residue
                                                                          transport route
                                                                          provenance name)
                                                                  | _ :: _ => none

private theorem observerAccumulationClock_round_trip :
    ∀ x : ObserverAccumulationClockUp,
      observerAccumulationClockFromEventFlow (observerAccumulationClockToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk present successor edge residue transport route provenance name =>
      change
        some
            (observerAccumulationClockDecodePacket
              (observerAccumulationClockEncodeBHist present)
              (observerAccumulationClockEncodeBHist successor)
              (observerAccumulationClockEncodeBHist edge)
              (observerAccumulationClockEncodeBHist residue)
              (observerAccumulationClockEncodeBHist transport)
              (observerAccumulationClockEncodeBHist route)
              (observerAccumulationClockEncodeBHist provenance)
              (observerAccumulationClockEncodeBHist name)) =
          some
            (ObserverAccumulationClockUp.mk present successor edge residue transport route
              provenance name)
      unfold observerAccumulationClockDecodePacket
      rw [observerAccumulationClockDecode_encode_bhist present,
        observerAccumulationClockDecode_encode_bhist successor,
        observerAccumulationClockDecode_encode_bhist edge,
        observerAccumulationClockDecode_encode_bhist residue,
        observerAccumulationClockDecode_encode_bhist transport,
        observerAccumulationClockDecode_encode_bhist route,
        observerAccumulationClockDecode_encode_bhist provenance,
        observerAccumulationClockDecode_encode_bhist name]

private theorem observerAccumulationClockToEventFlow_injective
    {x y : ObserverAccumulationClockUp} :
    observerAccumulationClockToEventFlow x = observerAccumulationClockToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerAccumulationClockFromEventFlow (observerAccumulationClockToEventFlow x) =
        observerAccumulationClockFromEventFlow (observerAccumulationClockToEventFlow y) :=
    congrArg observerAccumulationClockFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerAccumulationClock_round_trip x).symm
      (Eq.trans hread (observerAccumulationClock_round_trip y)))

instance observerAccumulationClockBHistCarrier : BHistCarrier ObserverAccumulationClockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerAccumulationClockToEventFlow
  fromEventFlow := observerAccumulationClockFromEventFlow

instance observerAccumulationClockChapterTasteGate :
    ChapterTasteGate ObserverAccumulationClockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerAccumulationClockFromEventFlow (observerAccumulationClockToEventFlow x) =
      some x
    exact observerAccumulationClock_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerAccumulationClockToEventFlow_injective heq)

instance observerAccumulationClockFieldFaithful : FieldFaithful ObserverAccumulationClockUp where
  fields := fun x =>
    match x with
    | ObserverAccumulationClockUp.mk present successor edge residue transport route provenance name =>
        [present, successor, edge, residue, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk present₁ successor₁ edge₁ residue₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk present₂ successor₂ edge₂ residue₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hPresent hTail₁
            injection hTail₁ with hSuccessor hTail₂
            injection hTail₂ with hEdge hTail₃
            injection hTail₃ with hResidue hTail₄
            injection hTail₄ with hTransport hTail₅
            injection hTail₅ with hRoute hTail₆
            injection hTail₆ with hProvenance hTail₇
            injection hTail₇ with hName _
            subst hPresent
            subst hSuccessor
            subst hEdge
            subst hResidue
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance observerAccumulationClockNontrivial : Nontrivial ObserverAccumulationClockUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverAccumulationClockUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObserverAccumulationClockUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverAccumulationClockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerAccumulationClockChapterTasteGate

theorem ObserverAccumulationClockTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerAccumulationClockDecodeBHist (observerAccumulationClockEncodeBHist h) = h) ∧
      (∀ x : ObserverAccumulationClockUp,
        observerAccumulationClockFromEventFlow (observerAccumulationClockToEventFlow x) = some x) ∧
        (∀ x y : ObserverAccumulationClockUp,
          observerAccumulationClockToEventFlow x =
            observerAccumulationClockToEventFlow y → x = y) ∧
          observerAccumulationClockEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerAccumulationClockDecode_encode_bhist
  · constructor
    · exact observerAccumulationClock_round_trip
    · constructor
      · intro x y heq
        exact observerAccumulationClockToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverAccumulationClockUp
