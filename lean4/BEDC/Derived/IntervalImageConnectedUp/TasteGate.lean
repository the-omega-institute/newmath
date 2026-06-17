import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalImageConnectedUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalImageConnectedUp : Type where
  | mk (I F V D L R W Q H C P N : BHist) : IntervalImageConnectedUp
  deriving DecidableEq

def intervalImageConnectedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalImageConnectedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalImageConnectedEncodeBHist h

def intervalImageConnectedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalImageConnectedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalImageConnectedDecodeBHist tail)

private theorem IntervalImageConnectedTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalImageConnectedFields : IntervalImageConnectedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalImageConnectedUp.mk I F V D L R W Q H C P N => [I, F, V, D, L, R, W, Q, H, C, P, N]

def intervalImageConnectedToEventFlow : IntervalImageConnectedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (intervalImageConnectedFields x).map intervalImageConnectedEncodeBHist

private def intervalImageConnectedEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalImageConnectedEventAt index rest

def intervalImageConnectedFromEventFlow (ef : EventFlow) : Option IntervalImageConnectedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalImageConnectedUp.mk
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 0 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 1 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 2 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 3 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 4 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 5 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 6 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 7 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 8 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 9 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 10 ef))
      (intervalImageConnectedDecodeBHist (intervalImageConnectedEventAt 11 ef)))

private theorem IntervalImageConnectedTasteGate_single_carrier_alignment_round_trip
    (x : IntervalImageConnectedUp) :
    intervalImageConnectedFromEventFlow (intervalImageConnectedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F V D L R W Q H C P N =>
      change
        some
          (IntervalImageConnectedUp.mk
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist I))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist F))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist V))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist D))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist L))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist R))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist W))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist Q))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist H))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist C))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist P))
            (intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist N))) =
          some (IntervalImageConnectedUp.mk I F V D L R W Q H C P N)
      rw [IntervalImageConnectedTasteGate_single_carrier_alignment_decode I,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode F,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode V,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode D,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode L,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode R,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode W,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode Q,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode H,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode C,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode P,
        IntervalImageConnectedTasteGate_single_carrier_alignment_decode N]

private theorem IntervalImageConnectedTasteGate_single_carrier_alignment_injective
    {x y : IntervalImageConnectedUp} :
    intervalImageConnectedToEventFlow x = intervalImageConnectedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalImageConnectedFromEventFlow (intervalImageConnectedToEventFlow x) =
        intervalImageConnectedFromEventFlow (intervalImageConnectedToEventFlow y) :=
    congrArg intervalImageConnectedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntervalImageConnectedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalImageConnectedTasteGate_single_carrier_alignment_round_trip y)))

private theorem IntervalImageConnectedTasteGate_single_carrier_alignment_fields :
    ∀ x y : IntervalImageConnectedUp,
      intervalImageConnectedFields x = intervalImageConnectedFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ V₁ D₁ L₁ R₁ W₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ F₂ V₂ D₂ L₂ R₂ W₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance intervalImageConnectedBHistCarrier : BHistCarrier IntervalImageConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalImageConnectedToEventFlow
  fromEventFlow := intervalImageConnectedFromEventFlow

instance intervalImageConnectedChapterTasteGate : ChapterTasteGate IntervalImageConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change intervalImageConnectedFromEventFlow (intervalImageConnectedToEventFlow x) = some x
    exact IntervalImageConnectedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalImageConnectedTasteGate_single_carrier_alignment_injective heq)

instance intervalImageConnectedFieldFaithful : FieldFaithful IntervalImageConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := intervalImageConnectedFields
  field_faithful := IntervalImageConnectedTasteGate_single_carrier_alignment_fields

instance intervalImageConnectedNontrivial : Nontrivial IntervalImageConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntervalImageConnectedUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntervalImageConnectedUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem IntervalImageConnectedTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalImageConnectedDecodeBHist (intervalImageConnectedEncodeBHist h) = h) ∧
      (∀ x : IntervalImageConnectedUp,
        intervalImageConnectedFromEventFlow (intervalImageConnectedToEventFlow x) = some x) ∧
        (∀ x y : IntervalImageConnectedUp,
          intervalImageConnectedToEventFlow x = intervalImageConnectedToEventFlow y → x = y) ∧
          intervalImageConnectedEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact IntervalImageConnectedTasteGate_single_carrier_alignment_decode
  constructor
  · exact IntervalImageConnectedTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact IntervalImageConnectedTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.IntervalImageConnectedUp
