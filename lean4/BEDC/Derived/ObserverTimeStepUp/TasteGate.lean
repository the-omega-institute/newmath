import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverTimeStepUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverTimeStepUp : Type where
  | mk : (source distinction cont transport refusal pkg name : BHist) → ObserverTimeStepUp

private def observerTimeStepEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerTimeStepEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerTimeStepEncodeBHist h

private def observerTimeStepDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerTimeStepDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerTimeStepDecodeBHist tail)

private theorem observerTimeStep_decode_encode_bhist :
    ∀ h : BHist, observerTimeStepDecodeBHist (observerTimeStepEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def observerTimeStepToEventFlow : ObserverTimeStepUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverTimeStepUp.mk source distinction cont transport refusal pkg name =>
      [[BMark.b0],
        observerTimeStepEncodeBHist source,
        [BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist distinction,
        [BMark.b1, BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist pkg,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerTimeStepEncodeBHist name]

private def observerTimeStepFromEventFlow : EventFlow → Option ObserverTimeStepUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, source, _tag1, distinction, _tag2, cont, _tag3, transport, _tag4, refusal,
      _tag5, pkg, _tag6, name] =>
      some
        (ObserverTimeStepUp.mk
          (observerTimeStepDecodeBHist source)
          (observerTimeStepDecodeBHist distinction)
          (observerTimeStepDecodeBHist cont)
          (observerTimeStepDecodeBHist transport)
          (observerTimeStepDecodeBHist refusal)
          (observerTimeStepDecodeBHist pkg)
          (observerTimeStepDecodeBHist name))
  | _ => none

private theorem observerTimeStep_round_trip :
    ∀ x : ObserverTimeStepUp,
      observerTimeStepFromEventFlow (observerTimeStepToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source distinction cont transport refusal pkg name =>
      change
        some
          (ObserverTimeStepUp.mk
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist source))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist distinction))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist cont))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist transport))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist refusal))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist pkg))
            (observerTimeStepDecodeBHist (observerTimeStepEncodeBHist name))) =
          some (ObserverTimeStepUp.mk source distinction cont transport refusal pkg name)
      rw [observerTimeStep_decode_encode_bhist source,
        observerTimeStep_decode_encode_bhist distinction,
        observerTimeStep_decode_encode_bhist cont,
        observerTimeStep_decode_encode_bhist transport,
        observerTimeStep_decode_encode_bhist refusal,
        observerTimeStep_decode_encode_bhist pkg,
        observerTimeStep_decode_encode_bhist name]

private theorem observerTimeStepToEventFlow_injective {x y : ObserverTimeStepUp} :
    observerTimeStepToEventFlow x = observerTimeStepToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerTimeStepFromEventFlow (observerTimeStepToEventFlow x) =
        observerTimeStepFromEventFlow (observerTimeStepToEventFlow y) :=
    congrArg observerTimeStepFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerTimeStep_round_trip x).symm
      (Eq.trans hread (observerTimeStep_round_trip y)))

private def observerTimeStepFields : ObserverTimeStepUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverTimeStepUp.mk source distinction cont transport refusal pkg name =>
      [source, distinction, cont, transport, refusal, pkg, name]

private theorem observerTimeStep_field_faithful :
    ∀ x y : ObserverTimeStepUp,
      observerTimeStepFields x = observerTimeStepFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ distinction₁ cont₁ transport₁ refusal₁ pkg₁ name₁ =>
      cases y with
      | mk source₂ distinction₂ cont₂ transport₂ refusal₂ pkg₂ name₂ =>
          cases h
          rfl

instance observerTimeStepBHistCarrier : BHistCarrier ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerTimeStepToEventFlow
  fromEventFlow := observerTimeStepFromEventFlow

instance observerTimeStepChapterTasteGate : ChapterTasteGate ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerTimeStepFromEventFlow (observerTimeStepToEventFlow x) = some x
    exact observerTimeStep_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerTimeStepToEventFlow_injective heq)

instance observerTimeStepFieldFaithful : FieldFaithful ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerTimeStepFields
  field_faithful := observerTimeStep_field_faithful

instance observerTimeStepNontrivial : Nontrivial ObserverTimeStepUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverTimeStepUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ObserverTimeStepUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverTimeStepUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerTimeStepChapterTasteGate

end BEDC.Derived.ObserverTimeStepUp
