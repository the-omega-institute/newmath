import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoquetGameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoquetGameUp : Type where
  | mk (B M L S R E T C P N : BHist) : ChoquetGameUp
  deriving DecidableEq

def choquetGameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choquetGameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choquetGameEncodeBHist h

def choquetGameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choquetGameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choquetGameDecodeBHist tail)

private theorem ChoquetGameTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, choquetGameDecodeBHist (choquetGameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def choquetGameFields : ChoquetGameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChoquetGameUp.mk B M L S R E T C P N => [B, M, L, S, R, E, T, C, P, N]

def choquetGameToEventFlow : ChoquetGameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (choquetGameFields x).map choquetGameEncodeBHist

private def choquetGameEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => choquetGameEventAt index rest

def choquetGameFromEventFlow : EventFlow → Option ChoquetGameUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (ChoquetGameUp.mk
          (choquetGameDecodeBHist (choquetGameEventAt 0 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 1 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 2 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 3 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 4 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 5 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 6 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 7 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 8 flow))
          (choquetGameDecodeBHist (choquetGameEventAt 9 flow)))

private theorem ChoquetGameTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChoquetGameUp,
      choquetGameFromEventFlow (choquetGameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M L S R E T C P N =>
      change
        some
          (ChoquetGameUp.mk
            (choquetGameDecodeBHist (choquetGameEncodeBHist B))
            (choquetGameDecodeBHist (choquetGameEncodeBHist M))
            (choquetGameDecodeBHist (choquetGameEncodeBHist L))
            (choquetGameDecodeBHist (choquetGameEncodeBHist S))
            (choquetGameDecodeBHist (choquetGameEncodeBHist R))
            (choquetGameDecodeBHist (choquetGameEncodeBHist E))
            (choquetGameDecodeBHist (choquetGameEncodeBHist T))
            (choquetGameDecodeBHist (choquetGameEncodeBHist C))
            (choquetGameDecodeBHist (choquetGameEncodeBHist P))
            (choquetGameDecodeBHist (choquetGameEncodeBHist N))) =
          some (ChoquetGameUp.mk B M L S R E T C P N)
      rw [ChoquetGameTasteGate_single_carrier_alignment_decode B,
        ChoquetGameTasteGate_single_carrier_alignment_decode M,
        ChoquetGameTasteGate_single_carrier_alignment_decode L,
        ChoquetGameTasteGate_single_carrier_alignment_decode S,
        ChoquetGameTasteGate_single_carrier_alignment_decode R,
        ChoquetGameTasteGate_single_carrier_alignment_decode E,
        ChoquetGameTasteGate_single_carrier_alignment_decode T,
        ChoquetGameTasteGate_single_carrier_alignment_decode C,
        ChoquetGameTasteGate_single_carrier_alignment_decode P,
        ChoquetGameTasteGate_single_carrier_alignment_decode N]

private theorem ChoquetGameTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChoquetGameUp} :
    choquetGameToEventFlow x = choquetGameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choquetGameFromEventFlow (choquetGameToEventFlow x) =
        choquetGameFromEventFlow (choquetGameToEventFlow y) :=
    congrArg choquetGameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ChoquetGameTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ChoquetGameTasteGate_single_carrier_alignment_round_trip y)))

instance choquetGameBHistCarrier : BHistCarrier ChoquetGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choquetGameToEventFlow
  fromEventFlow := choquetGameFromEventFlow

instance choquetGameChapterTasteGate : ChapterTasteGate ChoquetGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change choquetGameFromEventFlow (choquetGameToEventFlow x) = some x
    exact ChoquetGameTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChoquetGameTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance choquetGameFieldFaithful : FieldFaithful ChoquetGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := choquetGameFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk B1 M1 L1 S1 R1 E1 T1 C1 P1 N1 =>
        cases y with
        | mk B2 M2 L2 S2 R2 E2 T2 C2 P2 N2 =>
            cases hfields
            rfl

instance choquetGameNontrivial : BEDC.Meta.TasteGate.Nontrivial ChoquetGameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChoquetGameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChoquetGameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChoquetGameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  choquetGameChapterTasteGate

theorem ChoquetGameTasteGate_single_carrier_alignment :
    (∀ h : BHist, choquetGameDecodeBHist (choquetGameEncodeBHist h) = h) ∧
      (∀ x : ChoquetGameUp,
        choquetGameFromEventFlow (choquetGameToEventFlow x) = some x) ∧
        (∀ x y : ChoquetGameUp,
          choquetGameToEventFlow x = choquetGameToEventFlow y → x = y) ∧
          choquetGameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ChoquetGameTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ChoquetGameTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ChoquetGameTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.ChoquetGameUp
