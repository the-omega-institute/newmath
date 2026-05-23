import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealOrderTopologyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealOrderTopologyUp : Type where
  | mk (R A B S T H C P N : BHist) : RealOrderTopologyUp
  deriving DecidableEq

def realOrderTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realOrderTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realOrderTopologyEncodeBHist h

def realOrderTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realOrderTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realOrderTopologyDecodeBHist tail)

private theorem realOrderTopology_decode_encode_bhist :
    ∀ h : BHist, realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realOrderTopologyFields : RealOrderTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealOrderTopologyUp.mk R A B S T H C P N => [R, A, B, S, T, H, C, P, N]

def realOrderTopologyToEventFlow : RealOrderTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realOrderTopologyFields x).map realOrderTopologyEncodeBHist

private def realOrderTopologyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realOrderTopologyEventAt index rest

def realOrderTopologyFromEventFlow (ef : EventFlow) : Option RealOrderTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealOrderTopologyUp.mk
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 0 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 1 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 2 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 3 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 4 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 5 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 6 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 7 ef))
      (realOrderTopologyDecodeBHist (realOrderTopologyEventAt 8 ef)))

private theorem realOrderTopology_round_trip (x : RealOrderTopologyUp) :
    realOrderTopologyFromEventFlow (realOrderTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R A B S T H C P N =>
      change
        some
          (RealOrderTopologyUp.mk
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist R))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist A))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist B))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist S))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist T))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist H))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist C))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist P))
            (realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist N))) =
          some (RealOrderTopologyUp.mk R A B S T H C P N)
      rw [realOrderTopology_decode_encode_bhist R, realOrderTopology_decode_encode_bhist A,
        realOrderTopology_decode_encode_bhist B, realOrderTopology_decode_encode_bhist S,
        realOrderTopology_decode_encode_bhist T, realOrderTopology_decode_encode_bhist H,
        realOrderTopology_decode_encode_bhist C, realOrderTopology_decode_encode_bhist P,
        realOrderTopology_decode_encode_bhist N]

private theorem realOrderTopologyToEventFlow_injective {x y : RealOrderTopologyUp} :
    realOrderTopologyToEventFlow x = realOrderTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realOrderTopologyFromEventFlow (realOrderTopologyToEventFlow x) =
        realOrderTopologyFromEventFlow (realOrderTopologyToEventFlow y) :=
    congrArg realOrderTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realOrderTopology_round_trip x).symm
      (Eq.trans hread (realOrderTopology_round_trip y)))

private theorem realOrderTopology_fields_faithful :
    ∀ x y : RealOrderTopologyUp, realOrderTopologyFields x = realOrderTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 A1 B1 S1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 A2 B2 S2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realOrderTopologyBHistCarrier : BHistCarrier RealOrderTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realOrderTopologyToEventFlow
  fromEventFlow := realOrderTopologyFromEventFlow

instance realOrderTopologyChapterTasteGate : ChapterTasteGate RealOrderTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realOrderTopologyFromEventFlow (realOrderTopologyToEventFlow x) = some x
    exact realOrderTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realOrderTopologyToEventFlow_injective heq)

instance realOrderTopologyFieldFaithful : FieldFaithful RealOrderTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realOrderTopologyFields
  field_faithful := realOrderTopology_fields_faithful

instance realOrderTopologyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealOrderTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealOrderTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealOrderTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealOrderTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realOrderTopologyChapterTasteGate

theorem RealOrderTopologyTasteGate_single_carrier_alignment :
    (forall h : BHist, realOrderTopologyDecodeBHist (realOrderTopologyEncodeBHist h) = h) ∧
      (forall x : RealOrderTopologyUp,
        realOrderTopologyFromEventFlow (realOrderTopologyToEventFlow x) = some x) ∧
        (forall x y : RealOrderTopologyUp,
          realOrderTopologyToEventFlow x = realOrderTopologyToEventFlow y → x = y) ∧
          realOrderTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨realOrderTopology_decode_encode_bhist,
      realOrderTopology_round_trip,
      (fun _ _ heq => realOrderTopologyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealOrderTopologyUp.TasteGate
