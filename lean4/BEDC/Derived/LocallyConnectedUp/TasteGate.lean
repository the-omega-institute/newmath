import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyConnectedUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyConnectedUp : Type where
  | mk (T M G K B C H R P N : BHist) : LocallyConnectedUp
  deriving DecidableEq

def locallyConnectedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyConnectedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyConnectedEncodeBHist h

def locallyConnectedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyConnectedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyConnectedDecodeBHist tail)

private theorem LocallyConnectedTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locallyConnectedDecodeBHist (locallyConnectedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LocallyConnectedTasteGate_single_carrier_alignment_fields :
    LocallyConnectedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyConnectedUp.mk T M G K B C H R P N => [T, M, G, K, B, C, H, R, P, N]

def LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow :
    LocallyConnectedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (LocallyConnectedTasteGate_single_carrier_alignment_fields x).map
      locallyConnectedEncodeBHist

private def LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault index rest

def LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option LocallyConnectedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocallyConnectedUp.mk
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (locallyConnectedDecodeBHist
        (LocallyConnectedTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem LocallyConnectedTasteGate_single_carrier_alignment_round_trip
    (x : LocallyConnectedUp) :
    LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow
        (LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T M G K B C H R P N =>
      change
        some
          (LocallyConnectedUp.mk
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist T))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist M))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist G))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist K))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist B))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist C))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist H))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist R))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist P))
            (locallyConnectedDecodeBHist (locallyConnectedEncodeBHist N))) =
          some (LocallyConnectedUp.mk T M G K B C H R P N)
      rw [LocallyConnectedTasteGate_single_carrier_alignment_decode_encode T,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode M,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode G,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode K,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode B,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode C,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode H,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode R,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode P,
        LocallyConnectedTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocallyConnectedUp} :
    LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow x =
        LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow
          (LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow x) =
        LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow
          (LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocallyConnectedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocallyConnectedTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocallyConnectedTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocallyConnectedUp,
      LocallyConnectedTasteGate_single_carrier_alignment_fields x =
          LocallyConnectedTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 M1 G1 K1 B1 C1 H1 R1 P1 N1 =>
      cases y with
      | mk T2 M2 G2 K2 B2 C2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance locallyConnectedBHistCarrier : BHistCarrier LocallyConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow

instance locallyConnectedChapterTasteGate : ChapterTasteGate LocallyConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocallyConnectedTasteGate_single_carrier_alignment_fromEventFlow
          (LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact LocallyConnectedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocallyConnectedTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locallyConnectedFieldFaithful : FieldFaithful LocallyConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocallyConnectedTasteGate_single_carrier_alignment_fields
  field_faithful := LocallyConnectedTasteGate_single_carrier_alignment_fields_faithful

instance locallyConnectedNontrivial : Nontrivial LocallyConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocallyConnectedUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocallyConnectedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocallyConnectedTasteGate_single_carrier_alignment :
    (∀ h : BHist, locallyConnectedDecodeBHist (locallyConnectedEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocallyConnectedUp) ∧
        Nonempty (ChapterTasteGate LocallyConnectedUp) ∧
          Nonempty (FieldFaithful LocallyConnectedUp) ∧
            Nonempty (Nontrivial LocallyConnectedUp) ∧
              locallyConnectedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocallyConnectedTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨locallyConnectedBHistCarrier⟩,
        ⟨⟨locallyConnectedChapterTasteGate⟩,
          ⟨⟨locallyConnectedFieldFaithful⟩, ⟨⟨locallyConnectedNontrivial⟩, rfl⟩⟩⟩⟩⟩

end BEDC.Derived.LocallyConnectedUp.TasteGate
