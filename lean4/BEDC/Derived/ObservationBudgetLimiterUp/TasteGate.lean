import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationBudgetLimiterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationBudgetLimiterUp : Type where
  | mk (E B K W D R S H C P N : BHist) : ObservationBudgetLimiterUp
  deriving DecidableEq

def observationBudgetLimiterEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationBudgetLimiterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationBudgetLimiterEncodeBHist h

def observationBudgetLimiterDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationBudgetLimiterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationBudgetLimiterDecodeBHist tail)

private theorem observationBudgetLimiterDecode_encode_bhist :
    ∀ h : BHist,
      observationBudgetLimiterDecodeBHist
        (observationBudgetLimiterEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observationBudgetLimiter_mk_congr
    {E E' B B' K K' W W' D D' R R' S S' H H' C C' P P' N N' : BHist}
    (hE : E' = E)
    (hB : B' = B)
    (hK : K' = K)
    (hW : W' = W)
    (hD : D' = D)
    (hR : R' = R)
    (hS : S' = S)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    ObservationBudgetLimiterUp.mk E' B' K' W' D' R' S' H' C' P' N' =
      ObservationBudgetLimiterUp.mk E B K W D R S H C P N := by
  cases hE
  cases hB
  cases hK
  cases hW
  cases hD
  cases hR
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def observationBudgetLimiterToEventFlow :
    ObservationBudgetLimiterUp → EventFlow
  | ObservationBudgetLimiterUp.mk E B K W D R S H C P N =>
      [[BMark.b0],
        observationBudgetLimiterEncodeBHist E,
        [BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationBudgetLimiterEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationBudgetLimiterEncodeBHist N]

def observationBudgetLimiterFromEventFlow :
    EventFlow → Option ObservationBudgetLimiterUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | S :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ObservationBudgetLimiterUp.mk
                                                                                                  (observationBudgetLimiterDecodeBHist E)
                                                                                                  (observationBudgetLimiterDecodeBHist B)
                                                                                                  (observationBudgetLimiterDecodeBHist K)
                                                                                                  (observationBudgetLimiterDecodeBHist W)
                                                                                                  (observationBudgetLimiterDecodeBHist D)
                                                                                                  (observationBudgetLimiterDecodeBHist R)
                                                                                                  (observationBudgetLimiterDecodeBHist S)
                                                                                                  (observationBudgetLimiterDecodeBHist H)
                                                                                                  (observationBudgetLimiterDecodeBHist C)
                                                                                                  (observationBudgetLimiterDecodeBHist P)
                                                                                                  (observationBudgetLimiterDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem observationBudgetLimiter_round_trip :
    ∀ x : ObservationBudgetLimiterUp,
      observationBudgetLimiterFromEventFlow
        (observationBudgetLimiterToEventFlow x) = some x := by
  intro x
  cases x with
  | mk E B K W D R S H C P N =>
      change
        some
          (ObservationBudgetLimiterUp.mk
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist E))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist B))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist K))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist W))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist D))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist R))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist S))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist H))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist C))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist P))
            (observationBudgetLimiterDecodeBHist (observationBudgetLimiterEncodeBHist N))) =
          some (ObservationBudgetLimiterUp.mk E B K W D R S H C P N)
      exact
        congrArg some
          (observationBudgetLimiter_mk_congr
            (observationBudgetLimiterDecode_encode_bhist E)
            (observationBudgetLimiterDecode_encode_bhist B)
            (observationBudgetLimiterDecode_encode_bhist K)
            (observationBudgetLimiterDecode_encode_bhist W)
            (observationBudgetLimiterDecode_encode_bhist D)
            (observationBudgetLimiterDecode_encode_bhist R)
            (observationBudgetLimiterDecode_encode_bhist S)
            (observationBudgetLimiterDecode_encode_bhist H)
            (observationBudgetLimiterDecode_encode_bhist C)
            (observationBudgetLimiterDecode_encode_bhist P)
            (observationBudgetLimiterDecode_encode_bhist N))

private theorem observationBudgetLimiterToEventFlow_injective
    {x y : ObservationBudgetLimiterUp} :
    observationBudgetLimiterToEventFlow x =
      observationBudgetLimiterToEventFlow y → x = y := by
  intro heq
  have hread :
      observationBudgetLimiterFromEventFlow
          (observationBudgetLimiterToEventFlow x) =
        observationBudgetLimiterFromEventFlow
          (observationBudgetLimiterToEventFlow y) :=
    congrArg observationBudgetLimiterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationBudgetLimiter_round_trip x).symm
      (Eq.trans hread (observationBudgetLimiter_round_trip y)))

instance observationBudgetLimiterBHistCarrier :
    BHistCarrier ObservationBudgetLimiterUp where
  toEventFlow := observationBudgetLimiterToEventFlow
  fromEventFlow := observationBudgetLimiterFromEventFlow

instance observationBudgetLimiterChapterTasteGate :
    ChapterTasteGate ObservationBudgetLimiterUp where
  round_trip := by
    intro x
    change
      observationBudgetLimiterFromEventFlow
        (observationBudgetLimiterToEventFlow x) = some x
    exact observationBudgetLimiter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationBudgetLimiterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObservationBudgetLimiterUp :=
  inferInstance

def observationBudgetLimiterFields : ObservationBudgetLimiterUp → List BHist
  | ObservationBudgetLimiterUp.mk E B K W D R S H C P N => [E, B, K, W, D, R, S, H, C, P, N]

instance observationBudgetLimiterFieldFaithful :
    FieldFaithful ObservationBudgetLimiterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationBudgetLimiterFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk E B K W D R S H C P N =>
        cases y with
        | mk E' B' K' W' D' R' S' H' C' P' N' =>
            injection hfields with hE htail0
            injection htail0 with hB htail1
            injection htail1 with hK htail2
            injection htail2 with hW htail3
            injection htail3 with hD htail4
            injection htail4 with hR htail5
            injection htail5 with hS htail6
            injection htail6 with hH htail7
            injection htail7 with hC htail8
            injection htail8 with hP htail9
            injection htail9 with hN _hNil
            cases hE
            cases hB
            cases hK
            cases hW
            cases hD
            cases hR
            cases hS
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

theorem ObservationBudgetLimiter_kernel_scope_fields :
    observationBudgetLimiterFields
        (ObservationBudgetLimiterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
      [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      (∀ x y : ObservationBudgetLimiterUp,
        observationBudgetLimiterFields x = observationBudgetLimiterFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · exact FieldFaithful.field_faithful

theorem ObservationBudgetLimiterTasteGate_single_carrier_alignment :
    (∀ h : BHist, observationBudgetLimiterDecodeBHist
      (observationBudgetLimiterEncodeBHist h) = h) ∧
      (∀ x : ObservationBudgetLimiterUp,
        observationBudgetLimiterFromEventFlow
          (observationBudgetLimiterToEventFlow x) = some x) ∧
        (∀ x y : ObservationBudgetLimiterUp,
          observationBudgetLimiterToEventFlow x =
            observationBudgetLimiterToEventFlow y → x = y) ∧
          observationBudgetLimiterEncodeBHist BHist.Empty = ([] : List BMark) := by
  constructor
  · exact observationBudgetLimiterDecode_encode_bhist
  · constructor
    · exact observationBudgetLimiter_round_trip
    · constructor
      · intro x y heq
        exact observationBudgetLimiterToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObservationBudgetLimiterUp
