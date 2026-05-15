import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailCauchyRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailCauchyRouterUp : Type where
  | mk :
      (selector modulus window source limit endpoint transport cont pkg name : BHist) →
      TailCauchyRouterUp

private def tailCauchyRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailCauchyRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailCauchyRouterEncodeBHist h

private def tailCauchyRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailCauchyRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailCauchyRouterDecodeBHist tail)

private theorem tailCauchyRouter_decode_encode_bhist :
    ∀ h : BHist, tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def tailCauchyRouterToEventFlow : TailCauchyRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailCauchyRouterUp.mk selector modulus window source limit endpoint transport cont pkg name =>
      [[BMark.b0],
        tailCauchyRouterEncodeBHist selector,
        [BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist limit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tailCauchyRouterEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist pkg,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tailCauchyRouterEncodeBHist name]

private def tailCauchyRouterFromEventFlow : EventFlow → Option TailCauchyRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [_tag0, selector, _tag1, modulus, _tag2, window, _tag3, source, _tag4, limit,
      _tag5, endpoint, _tag6, transport, _tag7, cont, _tag8, pkg, _tag9, name] =>
      some
        (TailCauchyRouterUp.mk
          (tailCauchyRouterDecodeBHist selector)
          (tailCauchyRouterDecodeBHist modulus)
          (tailCauchyRouterDecodeBHist window)
          (tailCauchyRouterDecodeBHist source)
          (tailCauchyRouterDecodeBHist limit)
          (tailCauchyRouterDecodeBHist endpoint)
          (tailCauchyRouterDecodeBHist transport)
          (tailCauchyRouterDecodeBHist cont)
          (tailCauchyRouterDecodeBHist pkg)
          (tailCauchyRouterDecodeBHist name))
  | _ => none

private theorem tailCauchyRouter_round_trip :
    ∀ x : TailCauchyRouterUp,
      tailCauchyRouterFromEventFlow (tailCauchyRouterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selector modulus window source limit endpoint transport cont pkg name =>
      change
        some
          (TailCauchyRouterUp.mk
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist selector))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist modulus))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist window))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist source))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist limit))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist endpoint))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist transport))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist cont))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist pkg))
            (tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist name))) =
          some
            (TailCauchyRouterUp.mk selector modulus window source limit endpoint transport
              cont pkg name)
      rw [tailCauchyRouter_decode_encode_bhist selector,
        tailCauchyRouter_decode_encode_bhist modulus,
        tailCauchyRouter_decode_encode_bhist window,
        tailCauchyRouter_decode_encode_bhist source,
        tailCauchyRouter_decode_encode_bhist limit,
        tailCauchyRouter_decode_encode_bhist endpoint,
        tailCauchyRouter_decode_encode_bhist transport,
        tailCauchyRouter_decode_encode_bhist cont,
        tailCauchyRouter_decode_encode_bhist pkg,
        tailCauchyRouter_decode_encode_bhist name]

private theorem tailCauchyRouterToEventFlow_injective {x y : TailCauchyRouterUp} :
    tailCauchyRouterToEventFlow x = tailCauchyRouterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tailCauchyRouterFromEventFlow (tailCauchyRouterToEventFlow x) =
        tailCauchyRouterFromEventFlow (tailCauchyRouterToEventFlow y) :=
    congrArg tailCauchyRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tailCauchyRouter_round_trip x).symm
      (Eq.trans hread (tailCauchyRouter_round_trip y)))

private def tailCauchyRouterFields : TailCauchyRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailCauchyRouterUp.mk selector modulus window source limit endpoint transport cont pkg name =>
      [selector, modulus, window, source, limit, endpoint, transport, cont, pkg, name]

private theorem tailCauchyRouter_field_faithful :
    ∀ x y : TailCauchyRouterUp,
      tailCauchyRouterFields x = tailCauchyRouterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk selector₁ modulus₁ window₁ source₁ limit₁ endpoint₁ transport₁ cont₁ pkg₁ name₁ =>
      cases y with
      | mk selector₂ modulus₂ window₂ source₂ limit₂ endpoint₂ transport₂ cont₂ pkg₂ name₂ =>
          cases h
          rfl

instance tailCauchyRouterBHistCarrier : BHistCarrier TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailCauchyRouterToEventFlow
  fromEventFlow := tailCauchyRouterFromEventFlow

instance tailCauchyRouterChapterTasteGate : ChapterTasteGate TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tailCauchyRouterFromEventFlow (tailCauchyRouterToEventFlow x) = some x
    exact tailCauchyRouter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tailCauchyRouterToEventFlow_injective heq)

instance tailCauchyRouterFieldFaithful : FieldFaithful TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tailCauchyRouterFields
  field_faithful := tailCauchyRouter_field_faithful

instance tailCauchyRouterNontrivial : Nontrivial TailCauchyRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TailCauchyRouterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TailCauchyRouterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TailCauchyRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailCauchyRouterChapterTasteGate

end BEDC.Derived.TailCauchyRouterUp
