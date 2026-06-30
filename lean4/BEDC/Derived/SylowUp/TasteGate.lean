import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SylowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SylowUp : Type where
  | mk (G S p n W A T C H P N : BHist) : SylowUp
  deriving DecidableEq

def sylowEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sylowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sylowEncodeBHist h

def sylowDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sylowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sylowDecodeBHist tail)

private theorem SylowTasteGate_single_carrier_alignment_decode :
    forall h : BHist, sylowDecodeBHist (sylowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sylowFields : SylowUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SylowUp.mk G S p n W A T C H P N => [G, S, p, n, W, A, T, C, H, P, N]

def sylowToEventFlow : SylowUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sylowFields x).map sylowEncodeBHist

private def sylowEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sylowEventAtDefault index rest

def sylowFromEventFlow (ef : EventFlow) : Option SylowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SylowUp.mk
      (sylowDecodeBHist (sylowEventAtDefault 0 ef))
      (sylowDecodeBHist (sylowEventAtDefault 1 ef))
      (sylowDecodeBHist (sylowEventAtDefault 2 ef))
      (sylowDecodeBHist (sylowEventAtDefault 3 ef))
      (sylowDecodeBHist (sylowEventAtDefault 4 ef))
      (sylowDecodeBHist (sylowEventAtDefault 5 ef))
      (sylowDecodeBHist (sylowEventAtDefault 6 ef))
      (sylowDecodeBHist (sylowEventAtDefault 7 ef))
      (sylowDecodeBHist (sylowEventAtDefault 8 ef))
      (sylowDecodeBHist (sylowEventAtDefault 9 ef))
      (sylowDecodeBHist (sylowEventAtDefault 10 ef)))

private theorem SylowTasteGate_single_carrier_alignment_round_trip :
    forall x : SylowUp, sylowFromEventFlow (sylowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G S p n W A T C H P N =>
      change
        some
          (SylowUp.mk
            (sylowDecodeBHist (sylowEncodeBHist G))
            (sylowDecodeBHist (sylowEncodeBHist S))
            (sylowDecodeBHist (sylowEncodeBHist p))
            (sylowDecodeBHist (sylowEncodeBHist n))
            (sylowDecodeBHist (sylowEncodeBHist W))
            (sylowDecodeBHist (sylowEncodeBHist A))
            (sylowDecodeBHist (sylowEncodeBHist T))
            (sylowDecodeBHist (sylowEncodeBHist C))
            (sylowDecodeBHist (sylowEncodeBHist H))
            (sylowDecodeBHist (sylowEncodeBHist P))
            (sylowDecodeBHist (sylowEncodeBHist N))) =
          some (SylowUp.mk G S p n W A T C H P N)
      rw [SylowTasteGate_single_carrier_alignment_decode G,
        SylowTasteGate_single_carrier_alignment_decode S,
        SylowTasteGate_single_carrier_alignment_decode p,
        SylowTasteGate_single_carrier_alignment_decode n,
        SylowTasteGate_single_carrier_alignment_decode W,
        SylowTasteGate_single_carrier_alignment_decode A,
        SylowTasteGate_single_carrier_alignment_decode T,
        SylowTasteGate_single_carrier_alignment_decode C,
        SylowTasteGate_single_carrier_alignment_decode H,
        SylowTasteGate_single_carrier_alignment_decode P,
        SylowTasteGate_single_carrier_alignment_decode N]

private theorem sylowToEventFlow_injective {x y : SylowUp} :
    sylowToEventFlow x = sylowToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sylowFromEventFlow (sylowToEventFlow x) =
        sylowFromEventFlow (sylowToEventFlow y) :=
    congrArg sylowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SylowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SylowTasteGate_single_carrier_alignment_round_trip y)))

private theorem SylowTasteGate_single_carrier_alignment_fields :
    forall x y : SylowUp, sylowFields x = sylowFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance sylowBHistCarrier : BHistCarrier SylowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sylowToEventFlow
  fromEventFlow := sylowFromEventFlow

instance sylowChapterTasteGate : ChapterTasteGate SylowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sylowFromEventFlow (sylowToEventFlow x) = some x
    exact SylowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sylowToEventFlow_injective heq)

instance sylowFieldFaithful : FieldFaithful SylowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sylowFields
  field_faithful := SylowTasteGate_single_carrier_alignment_fields

instance sylowNontrivial : Nontrivial SylowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SylowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SylowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem SylowTasteGate_single_carrier_alignment :
    (forall h : BHist, sylowDecodeBHist (sylowEncodeBHist h) = h) ∧
      (forall x : SylowUp, sylowFromEventFlow (sylowToEventFlow x) = some x) ∧
        (forall x y : SylowUp, sylowToEventFlow x = sylowToEventFlow y -> x = y) ∧
          sylowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SylowTasteGate_single_carrier_alignment_decode,
      SylowTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => sylowToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SylowUp
