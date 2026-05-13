import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailFusionUp : Type where
  | mk (Q X W D T M R L H C P N : BHist) : RegularCauchyTailFusionUp
  deriving DecidableEq

def regularCauchyTailFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailFusionEncodeBHist h

def regularCauchyTailFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailFusionDecodeBHist tail)

private theorem regularCauchyTailFusionDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailFusionDecodeBHist
        (regularCauchyTailFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyTailFusion_mk_congr
    {Q Q' X X' W W' D D' T T' M M' R R' L L' H H' C C' P P' N N' : BHist}
    (hQ : Q' = Q)
    (hX : X' = X)
    (hW : W' = W)
    (hD : D' = D)
    (hT : T' = T)
    (hM : M' = M)
    (hR : R' = R)
    (hL : L' = L)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RegularCauchyTailFusionUp.mk Q' X' W' D' T' M' R' L' H' C' P' N' =
      RegularCauchyTailFusionUp.mk Q X W D T M R L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQ
  cases hX
  cases hW
  cases hD
  cases hT
  cases hM
  cases hR
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyTailFusionToEventFlow :
    RegularCauchyTailFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailFusionUp.mk Q X W D T M R L H C P N =>
      [[BMark.b0],
        regularCauchyTailFusionEncodeBHist Q,
        [BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTailFusionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTailFusionEncodeBHist N]

def regularCauchyTailFusionFromEventFlow :
    EventFlow → Option RegularCauchyTailFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | X :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | T :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | M :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | R :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | L :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | C :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (RegularCauchyTailFusionUp.mk
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            Q)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            X)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            W)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            D)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            T)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            M)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            R)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            L)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            H)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            C)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            P)
                                                                                                          (regularCauchyTailFusionDecodeBHist
                                                                                                            N))
                                                                                                  | _ :: _ => none

private theorem regularCauchyTailFusion_round_trip :
    ∀ x : RegularCauchyTailFusionUp,
      regularCauchyTailFusionFromEventFlow
        (regularCauchyTailFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q X W D T M R L H C P N =>
      change
        some
          (RegularCauchyTailFusionUp.mk
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist Q))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist X))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist W))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist D))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist T))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist M))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist R))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist L))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist H))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist C))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist P))
            (regularCauchyTailFusionDecodeBHist (regularCauchyTailFusionEncodeBHist N))) =
          some (RegularCauchyTailFusionUp.mk Q X W D T M R L H C P N)
      exact
        congrArg some
          (regularCauchyTailFusion_mk_congr
            (regularCauchyTailFusionDecode_encode_bhist Q)
            (regularCauchyTailFusionDecode_encode_bhist X)
            (regularCauchyTailFusionDecode_encode_bhist W)
            (regularCauchyTailFusionDecode_encode_bhist D)
            (regularCauchyTailFusionDecode_encode_bhist T)
            (regularCauchyTailFusionDecode_encode_bhist M)
            (regularCauchyTailFusionDecode_encode_bhist R)
            (regularCauchyTailFusionDecode_encode_bhist L)
            (regularCauchyTailFusionDecode_encode_bhist H)
            (regularCauchyTailFusionDecode_encode_bhist C)
            (regularCauchyTailFusionDecode_encode_bhist P)
            (regularCauchyTailFusionDecode_encode_bhist N))

private theorem regularCauchyTailFusionToEventFlow_injective
    {x y : RegularCauchyTailFusionUp} :
    regularCauchyTailFusionToEventFlow x =
      regularCauchyTailFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailFusionFromEventFlow
          (regularCauchyTailFusionToEventFlow x) =
        regularCauchyTailFusionFromEventFlow
          (regularCauchyTailFusionToEventFlow y) :=
    congrArg regularCauchyTailFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailFusion_round_trip x).symm
      (Eq.trans hread (regularCauchyTailFusion_round_trip y)))

instance regularCauchyTailFusionBHistCarrier :
    BHistCarrier RegularCauchyTailFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailFusionToEventFlow
  fromEventFlow := regularCauchyTailFusionFromEventFlow

instance regularCauchyTailFusionChapterTasteGate :
    ChapterTasteGate RegularCauchyTailFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailFusionFromEventFlow
        (regularCauchyTailFusionToEventFlow x) = some x
    exact regularCauchyTailFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailFusionToEventFlow_injective heq)

theorem RegularCauchyTailFusionTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyTailFusionDecodeBHist
      (regularCauchyTailFusionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailFusionUp,
        regularCauchyTailFusionFromEventFlow
          (regularCauchyTailFusionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailFusionUp,
          regularCauchyTailFusionToEventFlow x =
            regularCauchyTailFusionToEventFlow y → x = y) ∧
          regularCauchyTailFusionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTailFusionDecode_encode_bhist
  · constructor
    · exact regularCauchyTailFusion_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailFusionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyTailFusionUp
