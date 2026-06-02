import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstrateTraceInvariantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstrateTraceInvariantUp : Type where
  | mk (M A T W L R U H C P N : BHist) : SubstrateTraceInvariantUp

def substrateTraceInvariantEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substrateTraceInvariantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substrateTraceInvariantEncodeBHist h

def substrateTraceInvariantDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substrateTraceInvariantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substrateTraceInvariantDecodeBHist tail)

private theorem substrateTraceInvariant_decode_encode :
    forall h : BHist,
      substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def substrateTraceInvariantFields : SubstrateTraceInvariantUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubstrateTraceInvariantUp.mk M A T W L R U H C P N => [M, A, T, W, L, R, U, H, C, P, N]

def substrateTraceInvariantToEventFlow : SubstrateTraceInvariantUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (substrateTraceInvariantFields x).map substrateTraceInvariantEncodeBHist

private def substrateTraceInvariantEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => substrateTraceInvariantEventAt index rest

def substrateTraceInvariantFromEventFlow
    (ef : EventFlow) : Option SubstrateTraceInvariantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubstrateTraceInvariantUp.mk
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 0 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 1 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 2 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 3 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 4 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 5 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 6 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 7 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 8 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 9 ef))
      (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEventAt 10 ef)))

private theorem substrateTraceInvariant_round_trip (x : SubstrateTraceInvariantUp) :
    substrateTraceInvariantFromEventFlow (substrateTraceInvariantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M A T W L R U H C P N =>
      change
        some
          (SubstrateTraceInvariantUp.mk
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist M))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist A))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist T))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist W))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist L))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist R))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist U))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist H))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist C))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist P))
            (substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist N))) =
          some (SubstrateTraceInvariantUp.mk M A T W L R U H C P N)
      rw [substrateTraceInvariant_decode_encode M, substrateTraceInvariant_decode_encode A,
        substrateTraceInvariant_decode_encode T, substrateTraceInvariant_decode_encode W,
        substrateTraceInvariant_decode_encode L, substrateTraceInvariant_decode_encode R,
        substrateTraceInvariant_decode_encode U, substrateTraceInvariant_decode_encode H,
        substrateTraceInvariant_decode_encode C, substrateTraceInvariant_decode_encode P,
        substrateTraceInvariant_decode_encode N]

private theorem substrateTraceInvariantToEventFlow_injective
    {x y : SubstrateTraceInvariantUp} :
    substrateTraceInvariantToEventFlow x = substrateTraceInvariantToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substrateTraceInvariantFromEventFlow (substrateTraceInvariantToEventFlow x) =
        substrateTraceInvariantFromEventFlow (substrateTraceInvariantToEventFlow y) :=
    congrArg substrateTraceInvariantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (substrateTraceInvariant_round_trip x).symm
      (Eq.trans hread (substrateTraceInvariant_round_trip y)))

private theorem substrateTraceInvariantFields_faithful :
    forall x y : SubstrateTraceInvariantUp,
      substrateTraceInvariantFields x = substrateTraceInvariantFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ A₁ T₁ W₁ L₁ R₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ A₂ T₂ W₂ L₂ R₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance substrateTraceInvariantBHistCarrier : BHistCarrier SubstrateTraceInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substrateTraceInvariantToEventFlow
  fromEventFlow := substrateTraceInvariantFromEventFlow

instance substrateTraceInvariantChapterTasteGate :
    ChapterTasteGate SubstrateTraceInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      substrateTraceInvariantFromEventFlow (substrateTraceInvariantToEventFlow x) = some x
    exact substrateTraceInvariant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (substrateTraceInvariantToEventFlow_injective heq)

instance substrateTraceInvariantFieldFaithful :
    FieldFaithful SubstrateTraceInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := substrateTraceInvariantFields
  field_faithful := substrateTraceInvariantFields_faithful

instance substrateTraceInvariantNontrivial : Nontrivial SubstrateTraceInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubstrateTraceInvariantUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubstrateTraceInvariantUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def substrateTraceInvariantTasteGate : ChapterTasteGate SubstrateTraceInvariantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  substrateTraceInvariantChapterTasteGate

theorem SubstrateTraceInvariantTasteGate_single_carrier_alignment :
    (forall h : BHist,
      substrateTraceInvariantDecodeBHist (substrateTraceInvariantEncodeBHist h) = h) ∧
      (forall x : SubstrateTraceInvariantUp,
        substrateTraceInvariantFromEventFlow (substrateTraceInvariantToEventFlow x) = some x) ∧
        (forall x y : SubstrateTraceInvariantUp,
          substrateTraceInvariantToEventFlow x = substrateTraceInvariantToEventFlow y ->
            x = y) ∧
          substrateTraceInvariantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact substrateTraceInvariant_decode_encode
  · constructor
    · exact substrateTraceInvariant_round_trip
    · constructor
      · intro x y hxy
        exact substrateTraceInvariantToEventFlow_injective hxy
      · rfl

end BEDC.Derived.SubstrateTraceInvariantUp
