import BEDC.Derived.SeparatedCompletionReflectorUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def separatedCompletionReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedCompletionReflectorEncodeBHist h

def separatedCompletionReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedCompletionReflectorDecodeBHist tail)

private theorem SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedCompletionReflectorFields : SeparatedCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedCompletionReflectorUp.mk metricCompletion separatedMetric uniformCompletion
      universalProperty cauchyFilter cauchyNet tolerance realSeal transport replay provenance
      name =>
      [metricCompletion, separatedMetric, uniformCompletion, universalProperty, cauchyFilter,
        cauchyNet, tolerance, realSeal, transport, replay, provenance, name]

def separatedCompletionReflectorToEventFlow : SeparatedCompletionReflectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (separatedCompletionReflectorFields x).map separatedCompletionReflectorEncodeBHist

private def separatedCompletionReflectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedCompletionReflectorEventAtDefault index rest

def separatedCompletionReflectorFromEventFlow
    (ef : EventFlow) : Option SeparatedCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedCompletionReflectorUp.mk
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 0 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 1 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 2 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 3 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 4 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 5 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 6 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 7 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 8 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 9 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 10 ef))
      (separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEventAtDefault 11 ef)))

private theorem SeparatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedCompletionReflectorUp,
      separatedCompletionReflectorFromEventFlow
        (separatedCompletionReflectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk metricCompletion separatedMetric uniformCompletion universalProperty cauchyFilter
      cauchyNet tolerance realSeal transport replay provenance name =>
      change
        some
          (SeparatedCompletionReflectorUp.mk
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist metricCompletion))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist separatedMetric))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist uniformCompletion))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist universalProperty))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist cauchyFilter))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist cauchyNet))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist tolerance))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist realSeal))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist transport))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist replay))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist provenance))
            (separatedCompletionReflectorDecodeBHist
              (separatedCompletionReflectorEncodeBHist name))) =
          some
            (SeparatedCompletionReflectorUp.mk metricCompletion separatedMetric
              uniformCompletion universalProperty cauchyFilter cauchyNet tolerance realSeal
              transport replay provenance name)
      rw [SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode metricCompletion,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode separatedMetric,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode uniformCompletion,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode universalProperty,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode cauchyFilter,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode cauchyNet,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode tolerance,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode realSeal,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode transport,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode replay,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode provenance,
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode name]

private theorem SeparatedCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedCompletionReflectorUp} :
    separatedCompletionReflectorToEventFlow x =
      separatedCompletionReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedCompletionReflectorFromEventFlow (separatedCompletionReflectorToEventFlow x) =
        separatedCompletionReflectorFromEventFlow (separatedCompletionReflectorToEventFlow y) :=
    congrArg separatedCompletionReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeparatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparatedCompletionReflectorTasteGate_single_carrier_alignment_fields :
    ∀ x y : SeparatedCompletionReflectorUp,
      separatedCompletionReflectorFields x = separatedCompletionReflectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricCompletion₁ separatedMetric₁ uniformCompletion₁ universalProperty₁ cauchyFilter₁
      cauchyNet₁ tolerance₁ realSeal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk metricCompletion₂ separatedMetric₂ uniformCompletion₂ universalProperty₂ cauchyFilter₂
          cauchyNet₂ tolerance₂ realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hMetricCompletion tail0
          injection tail0 with hSeparatedMetric tail1
          injection tail1 with hUniformCompletion tail2
          injection tail2 with hUniversalProperty tail3
          injection tail3 with hCauchyFilter tail4
          injection tail4 with hCauchyNet tail5
          injection tail5 with hTolerance tail6
          injection tail6 with hRealSeal tail7
          injection tail7 with hTransport tail8
          injection tail8 with hReplay tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hName _
          subst hMetricCompletion
          subst hSeparatedMetric
          subst hUniformCompletion
          subst hUniversalProperty
          subst hCauchyFilter
          subst hCauchyNet
          subst hTolerance
          subst hRealSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance separatedCompletionReflectorBHistCarrier :
    BHistCarrier SeparatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedCompletionReflectorToEventFlow
  fromEventFlow := separatedCompletionReflectorFromEventFlow

instance separatedCompletionReflectorChapterTasteGate :
    ChapterTasteGate SeparatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedCompletionReflectorFromEventFlow (separatedCompletionReflectorToEventFlow x) =
        some x
    exact SeparatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance separatedCompletionReflectorFieldFaithful :
    FieldFaithful SeparatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedCompletionReflectorFields
  field_faithful := SeparatedCompletionReflectorTasteGate_single_carrier_alignment_fields

instance separatedCompletionReflectorNontrivial :
    Nontrivial SeparatedCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedCompletionReflectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SeparatedCompletionReflectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedCompletionReflectorChapterTasteGate

theorem SeparatedCompletionReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      separatedCompletionReflectorDecodeBHist
        (separatedCompletionReflectorEncodeBHist h) = h) ∧
      (∀ x : SeparatedCompletionReflectorUp,
        separatedCompletionReflectorFromEventFlow
          (separatedCompletionReflectorToEventFlow x) = some x) ∧
        (∀ x y : SeparatedCompletionReflectorUp,
          separatedCompletionReflectorToEventFlow x =
            separatedCompletionReflectorToEventFlow y → x = y) ∧
          separatedCompletionReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SeparatedCompletionReflectorTasteGate_single_carrier_alignment_decode,
      SeparatedCompletionReflectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SeparatedCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SeparatedCompletionReflectorUp
