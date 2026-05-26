import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNestedRealChoiceSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNestedRealChoiceSealUp : Type where
  | mk (I L C W R D E H T P N : BHist) : BoundedNestedRealChoiceSealUp
  deriving DecidableEq

def boundedNestedRealChoiceSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNestedRealChoiceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNestedRealChoiceSealEncodeBHist h

def boundedNestedRealChoiceSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNestedRealChoiceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNestedRealChoiceSealDecodeBHist tail)

private theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedNestedRealChoiceSealFields : BoundedNestedRealChoiceSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNestedRealChoiceSealUp.mk I L C W R D E H T P N =>
      [I, L, C, W, R, D, E, H, T, P, N]

def boundedNestedRealChoiceSealToEventFlow : BoundedNestedRealChoiceSealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedNestedRealChoiceSealFields x).map boundedNestedRealChoiceSealEncodeBHist

private def boundedNestedRealChoiceSealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedNestedRealChoiceSealEventAtDefault index rest

def boundedNestedRealChoiceSealFromEventFlow
    (ef : EventFlow) : Option BoundedNestedRealChoiceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedNestedRealChoiceSealUp.mk
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 0 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 1 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 2 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 3 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 4 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 5 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 6 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 7 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 8 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 9 ef))
      (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEventAtDefault 10 ef)))

private theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedNestedRealChoiceSealUp,
      boundedNestedRealChoiceSealFromEventFlow (boundedNestedRealChoiceSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L C W R D E H T P N =>
      change
        some
          (BoundedNestedRealChoiceSealUp.mk
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist I))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist L))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist C))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist W))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist R))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist D))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist E))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist H))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist T))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist P))
            (boundedNestedRealChoiceSealDecodeBHist (boundedNestedRealChoiceSealEncodeBHist N))) =
          some (BoundedNestedRealChoiceSealUp.mk I L C W R D E H T P N)
      rw [BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode I,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode L,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode C,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode W,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode R,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode D,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode E,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode H,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode T,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode P,
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode N]

private theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_injective
    {x y : BoundedNestedRealChoiceSealUp} :
    boundedNestedRealChoiceSealToEventFlow x = boundedNestedRealChoiceSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedNestedRealChoiceSealFromEventFlow (boundedNestedRealChoiceSealToEventFlow x) =
        boundedNestedRealChoiceSealFromEventFlow (boundedNestedRealChoiceSealToEventFlow y) :=
    congrArg boundedNestedRealChoiceSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedNestedRealChoiceSealUp,
      boundedNestedRealChoiceSealFields x = boundedNestedRealChoiceSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 L1 C1 W1 R1 D1 E1 H1 T1 P1 N1 =>
      cases y with
      | mk I2 L2 C2 W2 R2 D2 E2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance boundedNestedRealChoiceSealBHistCarrier :
    BHistCarrier BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNestedRealChoiceSealToEventFlow
  fromEventFlow := boundedNestedRealChoiceSealFromEventFlow

instance boundedNestedRealChoiceSealChapterTasteGate :
    ChapterTasteGate BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedNestedRealChoiceSealFromEventFlow
        (boundedNestedRealChoiceSealToEventFlow x) = some x
    exact BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_injective heq)

instance boundedNestedRealChoiceSealFieldFaithful :
    FieldFaithful BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedNestedRealChoiceSealFields
  field_faithful := BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_fields

instance boundedNestedRealChoiceSealNontrivial :
    Nontrivial BoundedNestedRealChoiceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedNestedRealChoiceSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedNestedRealChoiceSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedNestedRealChoiceSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedNestedRealChoiceSealChapterTasteGate

theorem BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedNestedRealChoiceSealUp) ∧
      Nonempty (FieldFaithful BoundedNestedRealChoiceSealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedNestedRealChoiceSealUp) ∧
          (∀ h : BHist,
            boundedNestedRealChoiceSealDecodeBHist
                (boundedNestedRealChoiceSealEncodeBHist h) =
              h) ∧
            (∀ x : BoundedNestedRealChoiceSealUp,
              boundedNestedRealChoiceSealFromEventFlow
                  (boundedNestedRealChoiceSealToEventFlow x) =
                some x) ∧
              (∀ x y : BoundedNestedRealChoiceSealUp,
                boundedNestedRealChoiceSealToEventFlow x =
                    boundedNestedRealChoiceSealToEventFlow y →
                  x = y) ∧
                boundedNestedRealChoiceSealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro boundedNestedRealChoiceSealChapterTasteGate,
      Nonempty.intro boundedNestedRealChoiceSealFieldFaithful,
      Nonempty.intro boundedNestedRealChoiceSealNontrivial,
      BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_decode,
      BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BoundedNestedRealChoiceSealTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BoundedNestedRealChoiceSealUp
