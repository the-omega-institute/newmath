import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteAutomatonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteAutomatonUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (states alphabet transition start accept word run endpoint classifier transport replay
      provenance name : BHist) : FiniteAutomatonUp
  deriving DecidableEq

def finiteAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteAutomatonEncodeBHist h

def finiteAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteAutomatonDecodeBHist tail)

private theorem FiniteAutomatonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteAutomatonDecodeBHist (finiteAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteAutomatonToEventFlow : FiniteAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteAutomatonUp.mk states alphabet transition start accept word run endpoint classifier
      transport replay provenance name =>
      [[BMark.b0],
        finiteAutomatonEncodeBHist states,
        [BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist alphabet,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist transition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist start,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist accept,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist word,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist run,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteAutomatonEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteAutomatonEncodeBHist name]

private def finiteAutomatonDecodePacket
    (states alphabet transition start accept word run endpoint classifier transport replay provenance
      name : RawEvent) : FiniteAutomatonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  FiniteAutomatonUp.mk
    (finiteAutomatonDecodeBHist states)
    (finiteAutomatonDecodeBHist alphabet)
    (finiteAutomatonDecodeBHist transition)
    (finiteAutomatonDecodeBHist start)
    (finiteAutomatonDecodeBHist accept)
    (finiteAutomatonDecodeBHist word)
    (finiteAutomatonDecodeBHist run)
    (finiteAutomatonDecodeBHist endpoint)
    (finiteAutomatonDecodeBHist classifier)
    (finiteAutomatonDecodeBHist transport)
    (finiteAutomatonDecodeBHist replay)
    (finiteAutomatonDecodeBHist provenance)
    (finiteAutomatonDecodeBHist name)

private def FiniteAutomatonTasteGate_single_carrier_alignment_readPair
    (ef : EventFlow) : Option (RawEvent × EventFlow) :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | value :: rest => some (value, rest)

def finiteAutomatonFromEventFlow : EventFlow → Option FiniteAutomatonUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      match FiniteAutomatonTasteGate_single_carrier_alignment_readPair ef with
      | none => none
      | some (states, rest0) =>
          match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest0 with
          | none => none
          | some (alphabet, rest1) =>
              match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest1 with
              | none => none
              | some (transition, rest2) =>
                  match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest2 with
                  | none => none
                  | some (start, rest3) =>
                      match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest3 with
                      | none => none
                      | some (accept, rest4) =>
                          match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest4 with
                          | none => none
                          | some (word, rest5) =>
                              match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest5 with
                              | none => none
                              | some (run, rest6) =>
                                  match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest6 with
                                  | none => none
                                  | some (endpoint, rest7) =>
                                      match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest7 with
                                      | none => none
                                      | some (classifier, rest8) =>
                                          match FiniteAutomatonTasteGate_single_carrier_alignment_readPair rest8 with
                                          | none => none
                                          | some (transport, rest9) =>
                                              match
                                                FiniteAutomatonTasteGate_single_carrier_alignment_readPair
                                                  rest9
                                              with
                                              | none => none
                                              | some (replay, rest10) =>
                                                  match
                                                    FiniteAutomatonTasteGate_single_carrier_alignment_readPair
                                                      rest10
                                                  with
                                                  | none => none
                                                  | some (provenance, rest11) =>
                                                      match
                                                        FiniteAutomatonTasteGate_single_carrier_alignment_readPair
                                                          rest11
                                                      with
                                                      | none => none
                                                      | some (name, rest12) =>
                                                          match rest12 with
                                                          | [] =>
                                                              some
                                                                (finiteAutomatonDecodePacket
                                                                  states alphabet transition
                                                                  start accept word run
                                                                  endpoint classifier transport
                                                                  replay provenance name)
                                                          | _ :: _ => none

private theorem FiniteAutomatonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteAutomatonUp,
      finiteAutomatonFromEventFlow (finiteAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk states alphabet transition start accept word run endpoint classifier transport replay
      provenance name =>
      change
        some
          (finiteAutomatonDecodePacket
            (finiteAutomatonEncodeBHist states)
            (finiteAutomatonEncodeBHist alphabet)
            (finiteAutomatonEncodeBHist transition)
            (finiteAutomatonEncodeBHist start)
            (finiteAutomatonEncodeBHist accept)
            (finiteAutomatonEncodeBHist word)
            (finiteAutomatonEncodeBHist run)
            (finiteAutomatonEncodeBHist endpoint)
            (finiteAutomatonEncodeBHist classifier)
            (finiteAutomatonEncodeBHist transport)
            (finiteAutomatonEncodeBHist replay)
            (finiteAutomatonEncodeBHist provenance)
            (finiteAutomatonEncodeBHist name)) =
          some
            (FiniteAutomatonUp.mk states alphabet transition start accept word run endpoint
              classifier transport replay provenance name)
      unfold finiteAutomatonDecodePacket
      rw [FiniteAutomatonTasteGate_single_carrier_alignment_decode states,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode alphabet,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode transition,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode start,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode accept,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode word,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode run,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode endpoint,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode classifier,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode transport,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode replay,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode provenance,
        FiniteAutomatonTasteGate_single_carrier_alignment_decode name]

private theorem FiniteAutomatonTasteGate_single_carrier_alignment_injective
    {x y : FiniteAutomatonUp} :
    finiteAutomatonToEventFlow x = finiteAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteAutomatonFromEventFlow (finiteAutomatonToEventFlow x) =
        finiteAutomatonFromEventFlow (finiteAutomatonToEventFlow y) :=
    congrArg finiteAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteAutomatonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteAutomatonTasteGate_single_carrier_alignment_round_trip y)))

instance finiteAutomatonBHistCarrier : BHistCarrier FiniteAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteAutomatonToEventFlow
  fromEventFlow := finiteAutomatonFromEventFlow

instance finiteAutomatonChapterTasteGate : ChapterTasteGate FiniteAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteAutomatonFromEventFlow (finiteAutomatonToEventFlow x) = some x
    exact FiniteAutomatonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteAutomatonTasteGate_single_carrier_alignment_injective heq)

instance finiteAutomatonFieldFaithful : FieldFaithful FiniteAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteAutomatonUp.mk states alphabet transition start accept word run endpoint classifier
        transport replay provenance name =>
        [states, alphabet, transition, start, accept, word, run, endpoint, classifier,
          transport, replay, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk states1 alphabet1 transition1 start1 accept1 word1 run1 endpoint1 classifier1
        transport1 replay1 provenance1 name1 =>
        cases y with
        | mk states2 alphabet2 transition2 start2 accept2 word2 run2 endpoint2 classifier2
            transport2 replay2 provenance2 name2 =>
            cases hfields
            rfl

instance finiteAutomatonNontrivial : Nontrivial FiniteAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteAutomatonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteAutomatonUp) ∧
      Nonempty (FieldFaithful FiniteAutomatonUp) ∧
        Nonempty (Nontrivial FiniteAutomatonUp) ∧
          (∀ h : BHist, finiteAutomatonDecodeBHist (finiteAutomatonEncodeBHist h) = h) ∧
            (∀ x : FiniteAutomatonUp,
              finiteAutomatonFromEventFlow (finiteAutomatonToEventFlow x) = some x) ∧
              (∀ x y : FiniteAutomatonUp,
                finiteAutomatonToEventFlow x = finiteAutomatonToEventFlow y → x = y) ∧
                finiteAutomatonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨finiteAutomatonChapterTasteGate⟩
  · constructor
    · exact ⟨finiteAutomatonFieldFaithful⟩
    · constructor
      · exact ⟨finiteAutomatonNontrivial⟩
      · constructor
        · exact FiniteAutomatonTasteGate_single_carrier_alignment_decode
        · constructor
          · exact FiniteAutomatonTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact FiniteAutomatonTasteGate_single_carrier_alignment_injective heq
            · rfl

end BEDC.Derived.FiniteAutomatonUp.TasteGate
