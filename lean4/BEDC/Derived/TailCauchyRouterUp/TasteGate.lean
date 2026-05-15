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
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selector :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | source :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | limit :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | endpoint :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | cont :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | pkg :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
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
                                                                                  | _ :: _ =>
                                                                                      none

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

theorem TailCauchyRouterTasteGate_single_carrier_alignment :
    (∀ h : BHist, tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist h) = h) ∧
      (∀ x : TailCauchyRouterUp,
        tailCauchyRouterFromEventFlow (tailCauchyRouterToEventFlow x) = some x) ∧
          tailCauchyRouterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have decodeRound :
      ∀ h : BHist, tailCauchyRouterDecodeBHist (tailCauchyRouterEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  constructor
  · exact decodeRound
  · constructor
    · intro x
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
          rw [decodeRound selector, decodeRound modulus, decodeRound window, decodeRound source,
            decodeRound limit, decodeRound endpoint, decodeRound transport, decodeRound cont,
            decodeRound pkg, decodeRound name]
    · rfl

end BEDC.Derived.TailCauchyRouterUp
