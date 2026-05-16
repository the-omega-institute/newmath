import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationReflectionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationReflectionSealUp : Type where
  | mk (P M S K C L H Q N : BHist) : FiniteObservationReflectionSealUp
  deriving DecidableEq

def finiteObservationReflectionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationReflectionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationReflectionSealEncodeBHist h

def finiteObservationReflectionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationReflectionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationReflectionSealDecodeBHist tail)

private theorem FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteObservationReflectionSealToEventFlow :
    FiniteObservationReflectionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationReflectionSealUp.mk P M S K C L H Q N =>
      [[BMark.b0],
        finiteObservationReflectionSealEncodeBHist P,
        [BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteObservationReflectionSealEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteObservationReflectionSealEncodeBHist N]

private def finiteObservationReflectionSealEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteObservationReflectionSealEventAtDefault index rest

def finiteObservationReflectionSealFromEventFlow
    (ef : EventFlow) : Option FiniteObservationReflectionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteObservationReflectionSealUp.mk
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 1 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 3 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 5 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 7 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 9 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 11 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 13 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 15 ef))
      (finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEventAtDefault 17 ef)))

private theorem FiniteObservationReflectionSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteObservationReflectionSealUp,
      finiteObservationReflectionSealFromEventFlow
        (finiteObservationReflectionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P M S K C L H Q N =>
      change
        some
          (FiniteObservationReflectionSealUp.mk
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist P))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist M))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist S))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist K))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist C))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist L))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist H))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist Q))
            (finiteObservationReflectionSealDecodeBHist
              (finiteObservationReflectionSealEncodeBHist N))) =
          some (FiniteObservationReflectionSealUp.mk P M S K C L H Q N)
      rw [FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode P,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode M,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode S,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode K,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode C,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode L,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode H,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode Q,
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode N]

private theorem FiniteObservationReflectionSealTasteGate_single_carrier_alignment_injective
    {x y : FiniteObservationReflectionSealUp} :
    finiteObservationReflectionSealToEventFlow x =
      finiteObservationReflectionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationReflectionSealFromEventFlow
          (finiteObservationReflectionSealToEventFlow x) =
        finiteObservationReflectionSealFromEventFlow
          (finiteObservationReflectionSealToEventFlow y) :=
    congrArg finiteObservationReflectionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteObservationReflectionSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteObservationReflectionSealTasteGate_single_carrier_alignment_round_trip y)))

private def finiteObservationReflectionSealFields :
    FiniteObservationReflectionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationReflectionSealUp.mk P M S K C L H Q N => [P, M, S, K, C, L, H, Q, N]

private theorem FiniteObservationReflectionSealTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteObservationReflectionSealUp,
      finiteObservationReflectionSealFields x = finiteObservationReflectionSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 M1 S1 K1 C1 L1 H1 Q1 N1 =>
      cases y with
      | mk P2 M2 S2 K2 C2 L2 H2 Q2 N2 =>
          cases hfields
          rfl

instance finiteObservationReflectionSealBHistCarrier :
    BHistCarrier FiniteObservationReflectionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationReflectionSealToEventFlow
  fromEventFlow := finiteObservationReflectionSealFromEventFlow

instance finiteObservationReflectionSealChapterTasteGate :
    ChapterTasteGate FiniteObservationReflectionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationReflectionSealFromEventFlow
        (finiteObservationReflectionSealToEventFlow x) = some x
    exact FiniteObservationReflectionSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteObservationReflectionSealTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteObservationReflectionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationReflectionSealChapterTasteGate

instance finiteObservationReflectionSealFieldFaithful :
    FieldFaithful FiniteObservationReflectionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationReflectionSealFields
  field_faithful :=
    FiniteObservationReflectionSealTasteGate_single_carrier_alignment_fields

instance finiteObservationReflectionSealNontrivial :
    Nontrivial FiniteObservationReflectionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationReflectionSealUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteObservationReflectionSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteObservationReflectionSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationReflectionSealDecodeBHist
        (finiteObservationReflectionSealEncodeBHist h) = h) ∧
      (∀ x : FiniteObservationReflectionSealUp,
        finiteObservationReflectionSealFromEventFlow
          (finiteObservationReflectionSealToEventFlow x) = some x) ∧
        (∀ x y : FiniteObservationReflectionSealUp,
          finiteObservationReflectionSealToEventFlow x =
            finiteObservationReflectionSealToEventFlow y → x = y) ∧
          finiteObservationReflectionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FiniteObservationReflectionSealTasteGate_single_carrier_alignment_decode,
      FiniteObservationReflectionSealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteObservationReflectionSealTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.FiniteObservationReflectionSealUp
