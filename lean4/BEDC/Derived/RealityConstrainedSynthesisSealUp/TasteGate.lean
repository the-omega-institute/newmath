import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSynthesisSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSynthesisSealUp : Type where
  | mk :
      (audit openFit objectivity observation explanation tower ledger failure transport replay
        provenance name : BHist) →
        RealityConstrainedSynthesisSealUp
  deriving DecidableEq

def realityConstrainedSynthesisSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSynthesisSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSynthesisSealEncodeBHist h

def realityConstrainedSynthesisSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSynthesisSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSynthesisSealDecodeBHist tail)

private theorem realityConstrainedSynthesisSeal_decode :
    ∀ h : BHist,
      realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedSynthesisSealFields :
    RealityConstrainedSynthesisSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation explanation
      tower ledger failure transport replay provenance name =>
      [audit, openFit, objectivity, observation, explanation, tower, ledger, failure,
        transport, replay, provenance, name]

def realityConstrainedSynthesisSealToEventFlow :
    RealityConstrainedSynthesisSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation explanation
      tower ledger failure transport replay provenance name =>
      [[BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist audit,
        [BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist openFit,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist objectivity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist explanation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist tower,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedSynthesisSealEncodeBHist name]

private def realityConstrainedSynthesisSealEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedSynthesisSealEventAtDefault index rest

def realityConstrainedSynthesisSealFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedSynthesisSealUp.mk
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 1 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 3 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 5 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 7 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 9 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 11 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 13 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 15 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 17 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 19 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 21 ef))
      (realityConstrainedSynthesisSealDecodeBHist
        (realityConstrainedSynthesisSealEventAtDefault 23 ef)))

private theorem realityConstrainedSynthesisSeal_round_trip :
    ∀ x : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk audit openFit objectivity observation explanation tower ledger failure transport
      replay provenance name =>
      change
        some
          (RealityConstrainedSynthesisSealUp.mk
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist audit))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist openFit))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist objectivity))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist observation))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist explanation))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist tower))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist ledger))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist failure))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist transport))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist replay))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist provenance))
            (realityConstrainedSynthesisSealDecodeBHist
              (realityConstrainedSynthesisSealEncodeBHist name))) =
          some
            (RealityConstrainedSynthesisSealUp.mk audit openFit objectivity observation
              explanation tower ledger failure transport replay provenance name)
      rw [realityConstrainedSynthesisSeal_decode audit,
        realityConstrainedSynthesisSeal_decode openFit,
        realityConstrainedSynthesisSeal_decode objectivity,
        realityConstrainedSynthesisSeal_decode observation,
        realityConstrainedSynthesisSeal_decode explanation,
        realityConstrainedSynthesisSeal_decode tower,
        realityConstrainedSynthesisSeal_decode ledger,
        realityConstrainedSynthesisSeal_decode failure,
        realityConstrainedSynthesisSeal_decode transport,
        realityConstrainedSynthesisSeal_decode replay,
        realityConstrainedSynthesisSeal_decode provenance,
        realityConstrainedSynthesisSeal_decode name]

private theorem realityConstrainedSynthesisSealToEventFlow_injective
    {x y : RealityConstrainedSynthesisSealUp} :
    realityConstrainedSynthesisSealToEventFlow x =
      realityConstrainedSynthesisSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow x) =
        realityConstrainedSynthesisSealFromEventFlow
          (realityConstrainedSynthesisSealToEventFlow y) :=
    congrArg realityConstrainedSynthesisSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (realityConstrainedSynthesisSeal_round_trip x).symm
      (Eq.trans hread (realityConstrainedSynthesisSeal_round_trip y)))

private theorem realityConstrainedSynthesisSeal_fields :
    ∀ x y : RealityConstrainedSynthesisSealUp,
      realityConstrainedSynthesisSealFields x = realityConstrainedSynthesisSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk audit₁ openFit₁ objectivity₁ observation₁ explanation₁ tower₁ ledger₁ failure₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk audit₂ openFit₂ objectivity₂ observation₂ explanation₂ tower₂ ledger₂ failure₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance realityConstrainedSynthesisSealBHistCarrier :
    BHistCarrier RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSynthesisSealToEventFlow
  fromEventFlow := realityConstrainedSynthesisSealFromEventFlow

instance realityConstrainedSynthesisSealChapterTasteGate :
    ChapterTasteGate RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSynthesisSealFromEventFlow
        (realityConstrainedSynthesisSealToEventFlow x) = some x
    exact realityConstrainedSynthesisSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSynthesisSealToEventFlow_injective heq)

instance realityConstrainedSynthesisSealFieldFaithful :
    FieldFaithful RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSynthesisSealFields
  field_faithful := realityConstrainedSynthesisSeal_fields

instance realityConstrainedSynthesisSealNontrivial :
    Nontrivial RealityConstrainedSynthesisSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSynthesisSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealityConstrainedSynthesisSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSynthesisSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSynthesisSealChapterTasteGate

end BEDC.Derived.RealityConstrainedSynthesisSealUp
