import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProgrammeStrengthLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProgrammeStrengthLedgerUp : Type where
  | mk
      (claimSite strength dependency status bridge refusal transport replay provenance name :
        BHist) :
      ProgrammeStrengthLedgerUp
  deriving DecidableEq

def programmeStrengthLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: programmeStrengthLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: programmeStrengthLedgerEncodeBHist h

def programmeStrengthLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (programmeStrengthLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (programmeStrengthLedgerDecodeBHist tail)

private theorem programmeStrengthLedger_decode_encode_bhist :
    ∀ h : BHist,
      programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def programmeStrengthLedgerFields :
    ProgrammeStrengthLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProgrammeStrengthLedgerUp.mk claimSite strength dependency status bridge refusal transport
      replay provenance name =>
      [claimSite, strength, dependency, status, bridge, refusal, transport, replay, provenance,
        name]

def programmeStrengthLedgerToEventFlow :
    ProgrammeStrengthLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProgrammeStrengthLedgerUp.mk claimSite strength dependency status bridge refusal transport
      replay provenance name =>
      [[BMark.b0],
        programmeStrengthLedgerEncodeBHist claimSite,
        [BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist strength,
        [BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist dependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist status,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist bridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        programmeStrengthLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        programmeStrengthLedgerEncodeBHist name]

private def programmeStrengthLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => programmeStrengthLedgerEventAtDefault index rest

def programmeStrengthLedgerFromEventFlow
    (ef : EventFlow) : Option ProgrammeStrengthLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProgrammeStrengthLedgerUp.mk
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 1 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 3 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 5 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 7 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 9 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 11 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 13 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 15 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 17 ef))
      (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEventAtDefault 19 ef)))

private theorem programmeStrengthLedger_round_trip :
    ∀ x : ProgrammeStrengthLedgerUp,
      programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claimSite strength dependency status bridge refusal transport replay provenance name =>
      change
        some
          (ProgrammeStrengthLedgerUp.mk
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist claimSite))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist strength))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist dependency))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist status))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist bridge))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist refusal))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist transport))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist replay))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist provenance))
            (programmeStrengthLedgerDecodeBHist (programmeStrengthLedgerEncodeBHist name))) =
          some
            (ProgrammeStrengthLedgerUp.mk claimSite strength dependency status bridge refusal
              transport replay provenance name)
      rw [programmeStrengthLedger_decode_encode_bhist claimSite,
        programmeStrengthLedger_decode_encode_bhist strength,
        programmeStrengthLedger_decode_encode_bhist dependency,
        programmeStrengthLedger_decode_encode_bhist status,
        programmeStrengthLedger_decode_encode_bhist bridge,
        programmeStrengthLedger_decode_encode_bhist refusal,
        programmeStrengthLedger_decode_encode_bhist transport,
        programmeStrengthLedger_decode_encode_bhist replay,
        programmeStrengthLedger_decode_encode_bhist provenance,
        programmeStrengthLedger_decode_encode_bhist name]

private theorem programmeStrengthLedgerToEventFlow_injective
    {x y : ProgrammeStrengthLedgerUp} :
    programmeStrengthLedgerToEventFlow x = programmeStrengthLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow x) =
        programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow y) :=
    congrArg programmeStrengthLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (programmeStrengthLedger_round_trip x).symm
      (Eq.trans hread (programmeStrengthLedger_round_trip y)))

private theorem programmeStrengthLedger_field_faithful :
    ∀ x y : ProgrammeStrengthLedgerUp,
      programmeStrengthLedgerFields x = programmeStrengthLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk claimSite strength dependency status bridge refusal transport replay provenance name =>
      cases y with
      | mk claimSite' strength' dependency' status' bridge' refusal' transport' replay'
          provenance' name' =>
          cases hfields
          rfl

instance programmeStrengthLedgerBHistCarrier :
    BHistCarrier ProgrammeStrengthLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := programmeStrengthLedgerToEventFlow
  fromEventFlow := programmeStrengthLedgerFromEventFlow

instance programmeStrengthLedgerChapterTasteGate :
    ChapterTasteGate ProgrammeStrengthLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow x) = some x
    exact programmeStrengthLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (programmeStrengthLedgerToEventFlow_injective heq)

instance programmeStrengthLedgerFieldFaithful :
    FieldFaithful ProgrammeStrengthLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := programmeStrengthLedgerFields
  field_faithful := programmeStrengthLedger_field_faithful

instance programmeStrengthLedgerNontrivial :
    Nontrivial ProgrammeStrengthLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProgrammeStrengthLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProgrammeStrengthLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProgrammeStrengthLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  programmeStrengthLedgerChapterTasteGate

theorem ProgrammeStrengthLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, programmeStrengthLedgerDecodeBHist
      (programmeStrengthLedgerEncodeBHist h) = h) ∧
      (∀ x : ProgrammeStrengthLedgerUp,
        programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow x) = some x) ∧
        (∀ x y : ProgrammeStrengthLedgerUp,
          programmeStrengthLedgerToEventFlow x = programmeStrengthLedgerToEventFlow y →
            x = y) ∧
          ∃ x : ProgrammeStrengthLedgerUp,
            x = ProgrammeStrengthLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
              programmeStrengthLedgerFromEventFlow (programmeStrengthLedgerToEventFlow x) =
                some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact programmeStrengthLedger_decode_encode_bhist
  · constructor
    · exact programmeStrengthLedger_round_trip
    · constructor
      · intro x y heq
        exact programmeStrengthLedgerToEventFlow_injective heq
      · refine ⟨ProgrammeStrengthLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, ?_, ?_⟩
        · rfl
        · exact programmeStrengthLedger_round_trip _

end BEDC.Derived.ProgrammeStrengthLedgerUp
