import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmptyFableMachineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmptyFableMachineUp : Type where
  | mk (emptyBoundary selectorWitness traceRow fableLedger transport replay provenance
      localName : BHist) : EmptyFableMachineUp
  deriving DecidableEq

def emptyFableMachineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: emptyFableMachineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: emptyFableMachineEncodeBHist h

def emptyFableMachineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (emptyFableMachineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (emptyFableMachineDecodeBHist tail)

private theorem emptyFableMachineDecode_encode_bhist :
    ∀ h : BHist, emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def emptyFableMachineToEventFlow : EmptyFableMachineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmptyFableMachineUp.mk emptyBoundary selectorWitness traceRow fableLedger transport
      replay provenance localName =>
      [[BMark.b0],
        emptyFableMachineEncodeBHist emptyBoundary,
        [BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist selectorWitness,
        [BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist traceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist fableLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        emptyFableMachineEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        emptyFableMachineEncodeBHist localName]

def emptyFableMachineFromEventFlow : EventFlow → Option EmptyFableMachineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | emptyBoundary :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | selectorWitness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | traceRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fableLedger :: rest7 =>
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
                                              | replay :: rest11 =>
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
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (EmptyFableMachineUp.mk
                                                                          (emptyFableMachineDecodeBHist
                                                                            emptyBoundary)
                                                                          (emptyFableMachineDecodeBHist
                                                                            selectorWitness)
                                                                          (emptyFableMachineDecodeBHist
                                                                            traceRow)
                                                                          (emptyFableMachineDecodeBHist
                                                                            fableLedger)
                                                                          (emptyFableMachineDecodeBHist
                                                                            transport)
                                                                          (emptyFableMachineDecodeBHist
                                                                            replay)
                                                                          (emptyFableMachineDecodeBHist
                                                                            provenance)
                                                                          (emptyFableMachineDecodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem emptyFableMachine_round_trip :
    ∀ x : EmptyFableMachineUp,
      emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk emptyBoundary selectorWitness traceRow fableLedger transport replay provenance
      localName =>
      change
        some
          (EmptyFableMachineUp.mk
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist emptyBoundary))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist selectorWitness))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist traceRow))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist fableLedger))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist transport))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist replay))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist provenance))
            (emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist localName))) =
          some
            (EmptyFableMachineUp.mk emptyBoundary selectorWitness traceRow fableLedger
              transport replay provenance localName)
      rw [emptyFableMachineDecode_encode_bhist emptyBoundary,
        emptyFableMachineDecode_encode_bhist selectorWitness,
        emptyFableMachineDecode_encode_bhist traceRow,
        emptyFableMachineDecode_encode_bhist fableLedger,
        emptyFableMachineDecode_encode_bhist transport,
        emptyFableMachineDecode_encode_bhist replay,
        emptyFableMachineDecode_encode_bhist provenance,
        emptyFableMachineDecode_encode_bhist localName]

private theorem emptyFableMachineToEventFlow_injective {x y : EmptyFableMachineUp} :
    emptyFableMachineToEventFlow x = emptyFableMachineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) =
        emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow y) :=
    congrArg emptyFableMachineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (emptyFableMachine_round_trip x).symm
      (Eq.trans hread (emptyFableMachine_round_trip y)))

instance emptyFableMachineBHistCarrier : BHistCarrier EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := emptyFableMachineToEventFlow
  fromEventFlow := emptyFableMachineFromEventFlow

instance emptyFableMachineChapterTasteGate : ChapterTasteGate EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x
    exact emptyFableMachine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (emptyFableMachineToEventFlow_injective heq)

instance emptyFableMachineFieldFaithful : FieldFaithful EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | EmptyFableMachineUp.mk emptyBoundary selectorWitness traceRow fableLedger transport
        replay provenance localName =>
        [emptyBoundary, selectorWitness, traceRow, fableLedger, transport, replay,
          provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk emptyBoundary₁ selectorWitness₁ traceRow₁ fableLedger₁ transport₁ replay₁
        provenance₁ localName₁ =>
        cases y with
        | mk emptyBoundary₂ selectorWitness₂ traceRow₂ fableLedger₂ transport₂ replay₂
            provenance₂ localName₂ =>
            simp only [] at h
            cases h
            rfl

instance emptyFableMachineNontrivial : Nontrivial EmptyFableMachineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmptyFableMachineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      EmptyFableMachineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EmptyFableMachineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  emptyFableMachineChapterTasteGate

theorem EmptyFableMachineTasteGate_single_carrier_alignment :
    (∀ h : BHist, emptyFableMachineDecodeBHist (emptyFableMachineEncodeBHist h) = h) /\
      (∀ x : EmptyFableMachineUp,
        emptyFableMachineFromEventFlow (emptyFableMachineToEventFlow x) = some x) /\
        (∀ x y : EmptyFableMachineUp,
          emptyFableMachineToEventFlow x = emptyFableMachineToEventFlow y -> x = y) /\
          Nonempty (ChapterTasteGate EmptyFableMachineUp) /\
            Nonempty (FieldFaithful EmptyFableMachineUp) /\
              Nonempty (Nontrivial EmptyFableMachineUp) /\
                emptyFableMachineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨emptyFableMachineDecode_encode_bhist, emptyFableMachine_round_trip,
      (fun _ _ heq => emptyFableMachineToEventFlow_injective heq),
      ⟨emptyFableMachineChapterTasteGate⟩, ⟨emptyFableMachineFieldFaithful⟩,
      ⟨emptyFableMachineNontrivial⟩, rfl⟩

end BEDC.Derived.EmptyFableMachineUp
