import BEDC.Derived.DarbouxOscillationCriterionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxOscillationCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def darbouxOscillationCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxOscillationCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxOscillationCriterionEncodeBHist h

def darbouxOscillationCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxOscillationCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxOscillationCriterionDecodeBHist tail)

private theorem darbouxOscillationCriterion_decode_encode_bhist :
    forall h : BHist,
      darbouxOscillationCriterionDecodeBHist
          (darbouxOscillationCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def darbouxOscillationCriterionToEventFlow :
    _root_.BEDC.Derived.DarbouxOscillationCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.DarbouxOscillationCriterionUp.mk integral sum lower upper oscillation
      partition regular realSeal transport replay provenance name =>
      [darbouxOscillationCriterionEncodeBHist integral,
        darbouxOscillationCriterionEncodeBHist sum,
        darbouxOscillationCriterionEncodeBHist lower,
        darbouxOscillationCriterionEncodeBHist upper,
        darbouxOscillationCriterionEncodeBHist oscillation,
        darbouxOscillationCriterionEncodeBHist partition,
        darbouxOscillationCriterionEncodeBHist regular,
        darbouxOscillationCriterionEncodeBHist realSeal,
        darbouxOscillationCriterionEncodeBHist transport,
        darbouxOscillationCriterionEncodeBHist replay,
        darbouxOscillationCriterionEncodeBHist provenance,
        darbouxOscillationCriterionEncodeBHist name]

def darbouxOscillationCriterionFromEventFlow :
    EventFlow -> Option _root_.BEDC.Derived.DarbouxOscillationCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | integral :: sum :: lower :: upper :: oscillation :: partition :: regular :: realSeal ::
      transport :: replay :: provenance :: name :: [] =>
      some
        (_root_.BEDC.Derived.DarbouxOscillationCriterionUp.mk
          (darbouxOscillationCriterionDecodeBHist integral)
          (darbouxOscillationCriterionDecodeBHist sum)
          (darbouxOscillationCriterionDecodeBHist lower)
          (darbouxOscillationCriterionDecodeBHist upper)
          (darbouxOscillationCriterionDecodeBHist oscillation)
          (darbouxOscillationCriterionDecodeBHist partition)
          (darbouxOscillationCriterionDecodeBHist regular)
          (darbouxOscillationCriterionDecodeBHist realSeal)
          (darbouxOscillationCriterionDecodeBHist transport)
          (darbouxOscillationCriterionDecodeBHist replay)
          (darbouxOscillationCriterionDecodeBHist provenance)
          (darbouxOscillationCriterionDecodeBHist name))
  | _ => none

private theorem darbouxOscillationCriterion_round_trip :
    forall x : _root_.BEDC.Derived.DarbouxOscillationCriterionUp,
      darbouxOscillationCriterionFromEventFlow
          (darbouxOscillationCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk integral sum lower upper oscillation partition regular realSeal transport replay
      provenance name =>
      change
        some
          (_root_.BEDC.Derived.DarbouxOscillationCriterionUp.mk
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist integral))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist sum))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist lower))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist upper))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist oscillation))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist partition))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist regular))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist realSeal))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist transport))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist replay))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist provenance))
            (darbouxOscillationCriterionDecodeBHist
              (darbouxOscillationCriterionEncodeBHist name))) =
          some
            (_root_.BEDC.Derived.DarbouxOscillationCriterionUp.mk integral sum lower upper
              oscillation partition regular realSeal transport replay provenance name)
      rw [darbouxOscillationCriterion_decode_encode_bhist integral,
        darbouxOscillationCriterion_decode_encode_bhist sum,
        darbouxOscillationCriterion_decode_encode_bhist lower,
        darbouxOscillationCriterion_decode_encode_bhist upper,
        darbouxOscillationCriterion_decode_encode_bhist oscillation,
        darbouxOscillationCriterion_decode_encode_bhist partition,
        darbouxOscillationCriterion_decode_encode_bhist regular,
        darbouxOscillationCriterion_decode_encode_bhist realSeal,
        darbouxOscillationCriterion_decode_encode_bhist transport,
        darbouxOscillationCriterion_decode_encode_bhist replay,
        darbouxOscillationCriterion_decode_encode_bhist provenance,
        darbouxOscillationCriterion_decode_encode_bhist name]

private theorem darbouxOscillationCriterionToEventFlow_injective
    {x y : _root_.BEDC.Derived.DarbouxOscillationCriterionUp} :
    darbouxOscillationCriterionToEventFlow x = darbouxOscillationCriterionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxOscillationCriterionFromEventFlow (darbouxOscillationCriterionToEventFlow x) =
        darbouxOscillationCriterionFromEventFlow (darbouxOscillationCriterionToEventFlow y) :=
    congrArg darbouxOscillationCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (darbouxOscillationCriterion_round_trip x).symm
      (Eq.trans hread (darbouxOscillationCriterion_round_trip y)))

instance darbouxOscillationCriterionBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.DarbouxOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxOscillationCriterionToEventFlow
  fromEventFlow := darbouxOscillationCriterionFromEventFlow

instance darbouxOscillationCriterionChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.DarbouxOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      darbouxOscillationCriterionFromEventFlow
          (darbouxOscillationCriterionToEventFlow x) =
        some x
    exact darbouxOscillationCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (darbouxOscillationCriterionToEventFlow_injective heq)

theorem DarbouxOscillationCriterionNamecertObligations
    (x : _root_.BEDC.Derived.DarbouxOscillationCriterionUp) :
    darbouxOscillationCriterionFromEventFlow (darbouxOscillationCriterionToEventFlow x) =
        some x ∧
      Nonempty (BHistCarrier _root_.BEDC.Derived.DarbouxOscillationCriterionUp) ∧
        Nonempty (ChapterTasteGate _root_.BEDC.Derived.DarbouxOscillationCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨darbouxOscillationCriterion_round_trip x,
      ⟨⟨darbouxOscillationCriterionBHistCarrier⟩,
        ⟨darbouxOscillationCriterionChapterTasteGate⟩⟩⟩

end BEDC.Derived.DarbouxOscillationCriterionUp
