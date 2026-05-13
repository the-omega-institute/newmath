import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusComparisonUp : Type where
  | mk : (M0 M1 T W Q E H C P N : BHist) → CauchyModulusComparisonUp
  deriving DecidableEq

def cauchyModulusComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusComparisonEncodeBHist h

def cauchyModulusComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusComparisonDecodeBHist tail)

private theorem cauchyModulusComparisonDecode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyModulusComparison_mk_congr
    {M0 M0' M1 M1' T T' W W' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hM0 : M0' = M0)
    (hM1 : M1' = M1)
    (hT : T' = T)
    (hW : W' = W)
    (hQ : Q' = Q)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    CauchyModulusComparisonUp.mk M0' M1' T' W' Q' E' H' C' P' N' =
      CauchyModulusComparisonUp.mk M0 M1 T W Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM0
  cases hM1
  cases hT
  cases hW
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyModulusComparisonToEventFlow : CauchyModulusComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusComparisonUp.mk M0 M1 T W Q E H C P N =>
      [[BMark.b0],
        cauchyModulusComparisonEncodeBHist M0,
        [BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist M1,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyModulusComparisonEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyModulusComparisonEncodeBHist N]

def cauchyModulusComparisonFromEventFlow : EventFlow → Option CauchyModulusComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | M1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
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
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | E :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (CauchyModulusComparisonUp.mk
                                                                                          (cauchyModulusComparisonDecodeBHist M0)
                                                                                          (cauchyModulusComparisonDecodeBHist M1)
                                                                                          (cauchyModulusComparisonDecodeBHist T)
                                                                                          (cauchyModulusComparisonDecodeBHist W)
                                                                                          (cauchyModulusComparisonDecodeBHist Q)
                                                                                          (cauchyModulusComparisonDecodeBHist E)
                                                                                          (cauchyModulusComparisonDecodeBHist H)
                                                                                          (cauchyModulusComparisonDecodeBHist C)
                                                                                          (cauchyModulusComparisonDecodeBHist P)
                                                                                          (cauchyModulusComparisonDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem cauchyModulusComparison_round_trip :
    ∀ x : CauchyModulusComparisonUp,
      cauchyModulusComparisonFromEventFlow (cauchyModulusComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M0 M1 T W Q E H C P N =>
      change
        some
          (CauchyModulusComparisonUp.mk
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist M0))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist M1))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist T))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist W))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist Q))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist E))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist H))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist C))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist P))
            (cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist N))) =
          some (CauchyModulusComparisonUp.mk M0 M1 T W Q E H C P N)
      exact
        congrArg some
          (cauchyModulusComparison_mk_congr
            (cauchyModulusComparisonDecode_encode_bhist M0)
            (cauchyModulusComparisonDecode_encode_bhist M1)
            (cauchyModulusComparisonDecode_encode_bhist T)
            (cauchyModulusComparisonDecode_encode_bhist W)
            (cauchyModulusComparisonDecode_encode_bhist Q)
            (cauchyModulusComparisonDecode_encode_bhist E)
            (cauchyModulusComparisonDecode_encode_bhist H)
            (cauchyModulusComparisonDecode_encode_bhist C)
            (cauchyModulusComparisonDecode_encode_bhist P)
            (cauchyModulusComparisonDecode_encode_bhist N))

private theorem cauchyModulusComparisonToEventFlow_injective {x y : CauchyModulusComparisonUp} :
    cauchyModulusComparisonToEventFlow x = cauchyModulusComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusComparisonFromEventFlow (cauchyModulusComparisonToEventFlow x) =
        cauchyModulusComparisonFromEventFlow (cauchyModulusComparisonToEventFlow y) :=
    congrArg cauchyModulusComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusComparison_round_trip x).symm
      (Eq.trans hread (cauchyModulusComparison_round_trip y)))

instance cauchyModulusComparisonBHistCarrier : BHistCarrier CauchyModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusComparisonToEventFlow
  fromEventFlow := cauchyModulusComparisonFromEventFlow

instance cauchyModulusComparisonChapterTasteGate :
    ChapterTasteGate CauchyModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusComparisonFromEventFlow (cauchyModulusComparisonToEventFlow x) = some x
    exact cauchyModulusComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusComparisonToEventFlow_injective heq)

theorem CauchyModulusComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusComparisonDecodeBHist (cauchyModulusComparisonEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusComparisonUp,
        cauchyModulusComparisonFromEventFlow (cauchyModulusComparisonToEventFlow x) = some x) ∧
        (∀ x y : CauchyModulusComparisonUp,
          cauchyModulusComparisonToEventFlow x = cauchyModulusComparisonToEventFlow y → x = y) ∧
          cauchyModulusComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyModulusComparisonDecode_encode_bhist
  · constructor
    · exact cauchyModulusComparison_round_trip
    · constructor
      · intro x y heq
        exact cauchyModulusComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyModulusComparisonUp
