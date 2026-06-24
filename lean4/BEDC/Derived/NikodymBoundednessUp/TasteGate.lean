import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NikodymBoundednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NikodymBoundednessUp : Type where
  | mk (M A F W T B D R H C P N : BHist) : NikodymBoundednessUp
  deriving DecidableEq

def nikodymBoundednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nikodymBoundednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nikodymBoundednessEncodeBHist h

def nikodymBoundednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nikodymBoundednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nikodymBoundednessDecodeBHist tail)

private theorem nikodymBoundedness_decode_encode_bhist :
    ∀ h : BHist,
      nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nikodymBoundednessFields : NikodymBoundednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NikodymBoundednessUp.mk M A F W T B D R H C P N =>
      [M, A, F, W, T, B, D, R, H, C, P, N]

def nikodymBoundednessToEventFlow : NikodymBoundednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map nikodymBoundednessEncodeBHist (nikodymBoundednessFields x)

private def nikodymBoundednessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nikodymBoundednessEventAtDefault index rest

def nikodymBoundednessFromEventFlow (ef : EventFlow) : Option NikodymBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NikodymBoundednessUp.mk
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 0 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 1 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 2 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 3 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 4 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 5 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 6 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 7 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 8 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 9 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 10 ef))
      (nikodymBoundednessDecodeBHist (nikodymBoundednessEventAtDefault 11 ef)))

private theorem nikodymBoundedness_round_trip :
    ∀ x : NikodymBoundednessUp,
      nikodymBoundednessFromEventFlow (nikodymBoundednessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M A F W T B D R H C P N =>
      change
        some
          (NikodymBoundednessUp.mk
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist M))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist A))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist F))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist W))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist T))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist B))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist D))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist R))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist H))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist C))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist P))
            (nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist N))) =
          some (NikodymBoundednessUp.mk M A F W T B D R H C P N)
      rw [nikodymBoundedness_decode_encode_bhist M,
        nikodymBoundedness_decode_encode_bhist A,
        nikodymBoundedness_decode_encode_bhist F,
        nikodymBoundedness_decode_encode_bhist W,
        nikodymBoundedness_decode_encode_bhist T,
        nikodymBoundedness_decode_encode_bhist B,
        nikodymBoundedness_decode_encode_bhist D,
        nikodymBoundedness_decode_encode_bhist R,
        nikodymBoundedness_decode_encode_bhist H,
        nikodymBoundedness_decode_encode_bhist C,
        nikodymBoundedness_decode_encode_bhist P,
        nikodymBoundedness_decode_encode_bhist N]

private theorem nikodymBoundednessToEventFlow_injective {x y : NikodymBoundednessUp} :
    nikodymBoundednessToEventFlow x = nikodymBoundednessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nikodymBoundednessFromEventFlow (nikodymBoundednessToEventFlow x) =
        nikodymBoundednessFromEventFlow (nikodymBoundednessToEventFlow y) :=
    congrArg nikodymBoundednessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nikodymBoundedness_round_trip x).symm
      (Eq.trans hread (nikodymBoundedness_round_trip y)))

private theorem nikodymBoundedness_fields_faithful :
    ∀ x y : NikodymBoundednessUp,
      nikodymBoundednessFields x = nikodymBoundednessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 A1 F1 W1 T1 B1 D1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 A2 F2 W2 T2 B2 D2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance nikodymBoundednessBHistCarrier : BHistCarrier NikodymBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nikodymBoundednessToEventFlow
  fromEventFlow := nikodymBoundednessFromEventFlow

instance nikodymBoundednessChapterTasteGate :
    ChapterTasteGate NikodymBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nikodymBoundednessFromEventFlow (nikodymBoundednessToEventFlow x) = some x
    exact nikodymBoundedness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nikodymBoundednessToEventFlow_injective heq)

instance nikodymBoundednessFieldFaithful : FieldFaithful NikodymBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nikodymBoundednessFields
  field_faithful := nikodymBoundedness_fields_faithful

instance nikodymBoundednessNontrivial : Nontrivial NikodymBoundednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NikodymBoundednessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NikodymBoundednessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NikodymBoundednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nikodymBoundednessChapterTasteGate

theorem NikodymBoundednessTasteGate_single_carrier_alignment :
    (forall h : BHist,
      nikodymBoundednessDecodeBHist (nikodymBoundednessEncodeBHist h) = h) /\
      (forall x : NikodymBoundednessUp,
        nikodymBoundednessFromEventFlow (nikodymBoundednessToEventFlow x) = some x) /\
        (forall x y : NikodymBoundednessUp,
          nikodymBoundednessToEventFlow x = nikodymBoundednessToEventFlow y -> x = y) /\
          nikodymBoundednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨nikodymBoundedness_decode_encode_bhist, nikodymBoundedness_round_trip,
      (fun _ _ heq => nikodymBoundednessToEventFlow_injective heq), rfl⟩

end BEDC.Derived.NikodymBoundednessUp
