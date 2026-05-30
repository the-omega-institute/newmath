import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricClosureUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (M T S L U W R E H C P N : BHist) : MetricClosureUp
  deriving DecidableEq

def metricClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricClosureEncodeBHist h

def metricClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricClosureDecodeBHist tail)

private theorem metricClosure_decode_encode_bhist :
    ∀ h : BHist,
      metricClosureDecodeBHist (metricClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricClosureToEventFlow : MetricClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricClosureUp.mk M T S L U W R E H C P N =>
      [metricClosureEncodeBHist M,
        metricClosureEncodeBHist T,
        metricClosureEncodeBHist S,
        metricClosureEncodeBHist L,
        metricClosureEncodeBHist U,
        metricClosureEncodeBHist W,
        metricClosureEncodeBHist R,
        metricClosureEncodeBHist E,
        metricClosureEncodeBHist H,
        metricClosureEncodeBHist C,
        metricClosureEncodeBHist P,
        metricClosureEncodeBHist N]

private def metricClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricClosureEventAtDefault index rest

def metricClosureFromEventFlow
    (ef : EventFlow) : Option MetricClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricClosureUp.mk
      (metricClosureDecodeBHist (metricClosureEventAtDefault 0 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 1 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 2 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 3 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 4 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 5 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 6 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 7 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 8 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 9 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 10 ef))
      (metricClosureDecodeBHist (metricClosureEventAtDefault 11 ef)))

private theorem metricClosure_round_trip :
    ∀ x : MetricClosureUp,
      metricClosureFromEventFlow (metricClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T S L U W R E H C P N =>
      change
        some
            (MetricClosureUp.mk
              (metricClosureDecodeBHist (metricClosureEncodeBHist M))
              (metricClosureDecodeBHist (metricClosureEncodeBHist T))
              (metricClosureDecodeBHist (metricClosureEncodeBHist S))
              (metricClosureDecodeBHist (metricClosureEncodeBHist L))
              (metricClosureDecodeBHist (metricClosureEncodeBHist U))
              (metricClosureDecodeBHist (metricClosureEncodeBHist W))
              (metricClosureDecodeBHist (metricClosureEncodeBHist R))
              (metricClosureDecodeBHist (metricClosureEncodeBHist E))
              (metricClosureDecodeBHist (metricClosureEncodeBHist H))
              (metricClosureDecodeBHist (metricClosureEncodeBHist C))
              (metricClosureDecodeBHist (metricClosureEncodeBHist P))
              (metricClosureDecodeBHist (metricClosureEncodeBHist N))) =
          some (MetricClosureUp.mk M T S L U W R E H C P N)
      rw [metricClosure_decode_encode_bhist M,
        metricClosure_decode_encode_bhist T,
        metricClosure_decode_encode_bhist S,
        metricClosure_decode_encode_bhist L,
        metricClosure_decode_encode_bhist U,
        metricClosure_decode_encode_bhist W,
        metricClosure_decode_encode_bhist R,
        metricClosure_decode_encode_bhist E,
        metricClosure_decode_encode_bhist H,
        metricClosure_decode_encode_bhist C,
        metricClosure_decode_encode_bhist P,
        metricClosure_decode_encode_bhist N]

private theorem metricClosureToEventFlow_injective
    {x y : MetricClosureUp} :
    metricClosureToEventFlow x = metricClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricClosureFromEventFlow (metricClosureToEventFlow x) =
        metricClosureFromEventFlow (metricClosureToEventFlow y) :=
    congrArg metricClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricClosure_round_trip x).symm
      (Eq.trans hread (metricClosure_round_trip y)))

def metricClosureFields : MetricClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricClosureUp.mk M T S L U W R E H C P N => [M, T, S, L, U, W, R, E, H, C, P, N]

private theorem metricClosure_fields_faithful :
    ∀ x y : MetricClosureUp,
      metricClosureFields x = metricClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M T S L U W R E H C P N =>
      cases y with
      | mk M' T' S' L' U' W' R' E' H' C' P' N' =>
          simp only [metricClosureFields] at h
          cases h
          rfl

instance metricClosureBHistCarrier : BHistCarrier MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricClosureToEventFlow
  fromEventFlow := metricClosureFromEventFlow

instance metricClosureChapterTasteGate : ChapterTasteGate MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricClosureFromEventFlow (metricClosureToEventFlow x) = some x
    exact metricClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricClosureToEventFlow_injective heq)

instance metricClosureFieldFaithful : FieldFaithful MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricClosureFields
  field_faithful := metricClosure_fields_faithful

instance metricClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetricClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricClosureChapterTasteGate

theorem MetricClosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricClosureUp) ∧
      Nonempty (FieldFaithful MetricClosureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetricClosureUp) ∧
          (∀ h : BHist,
            metricClosureDecodeBHist (metricClosureEncodeBHist h) = h) ∧
            (∀ x : MetricClosureUp,
              metricClosureFromEventFlow (metricClosureToEventFlow x) =
                some x) ∧
              (∀ x y : MetricClosureUp,
                metricClosureToEventFlow x = metricClosureToEventFlow y →
                  x = y) ∧
                metricClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨metricClosureChapterTasteGate⟩,
      ⟨metricClosureFieldFaithful⟩,
      ⟨metricClosureNontrivial⟩,
      metricClosure_decode_encode_bhist,
      metricClosure_round_trip,
      (fun _ _ heq => metricClosureToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricClosureUp
