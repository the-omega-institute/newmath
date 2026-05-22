import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCeilingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCeilingUp : Type where
  | mk : (x k c p l u M R E H T P N : BHist) → DyadicCeilingUp
  deriving DecidableEq

def dyadicCeilingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCeilingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCeilingEncodeBHist h

def dyadicCeilingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCeilingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCeilingDecodeBHist tail)

private theorem dyadicCeiling_decode_encode_bhist :
    ∀ h : BHist, dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicCeilingToEventFlow : DyadicCeilingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCeilingUp.mk x k c p l u M R E H T P N =>
      [[BMark.b0],
        dyadicCeilingEncodeBHist x,
        [BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist k,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist l,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist u,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicCeilingEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicCeilingEncodeBHist N]

def dyadicCeilingFromEventFlow :
    EventFlow → Option DyadicCeilingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | x :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | k :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | c :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | p :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | l :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | u :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | M :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | R :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | E :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | H :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | T :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | P :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | N :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (DyadicCeilingUp.mk
                                                                                                                  (dyadicCeilingDecodeBHist x)
                                                                                                                  (dyadicCeilingDecodeBHist k)
                                                                                                                  (dyadicCeilingDecodeBHist c)
                                                                                                                  (dyadicCeilingDecodeBHist p)
                                                                                                                  (dyadicCeilingDecodeBHist l)
                                                                                                                  (dyadicCeilingDecodeBHist u)
                                                                                                                  (dyadicCeilingDecodeBHist M)
                                                                                                                  (dyadicCeilingDecodeBHist R)
                                                                                                                  (dyadicCeilingDecodeBHist E)
                                                                                                                  (dyadicCeilingDecodeBHist H)
                                                                                                                  (dyadicCeilingDecodeBHist T)
                                                                                                                  (dyadicCeilingDecodeBHist P)
                                                                                                                  (dyadicCeilingDecodeBHist N))
                                                                                                          | _ :: _ => none

private theorem dyadicCeiling_round_trip :
    ∀ x : DyadicCeilingUp,
      dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro packet
  cases packet with
  | mk x k c p l u M R E H T P N =>
      change
        some
          (DyadicCeilingUp.mk
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist x))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist k))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist c))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist p))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist l))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist u))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist M))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist R))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist E))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist H))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist T))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist P))
            (dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist N))) =
          some (DyadicCeilingUp.mk x k c p l u M R E H T P N)
      rw [dyadicCeiling_decode_encode_bhist x,
        dyadicCeiling_decode_encode_bhist k,
        dyadicCeiling_decode_encode_bhist c,
        dyadicCeiling_decode_encode_bhist p,
        dyadicCeiling_decode_encode_bhist l,
        dyadicCeiling_decode_encode_bhist u,
        dyadicCeiling_decode_encode_bhist M,
        dyadicCeiling_decode_encode_bhist R,
        dyadicCeiling_decode_encode_bhist E,
        dyadicCeiling_decode_encode_bhist H,
        dyadicCeiling_decode_encode_bhist T,
        dyadicCeiling_decode_encode_bhist P,
        dyadicCeiling_decode_encode_bhist N]

private theorem dyadicCeilingToEventFlow_injective
    {x y : DyadicCeilingUp} :
    dyadicCeilingToEventFlow x = dyadicCeilingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) =
        dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow y) :=
    congrArg dyadicCeilingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicCeiling_round_trip x).symm
      (Eq.trans hread (dyadicCeiling_round_trip y)))

instance dyadicCeilingBHistCarrier : BHistCarrier DyadicCeilingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCeilingToEventFlow
  fromEventFlow := dyadicCeilingFromEventFlow

instance dyadicCeilingChapterTasteGate :
    ChapterTasteGate DyadicCeilingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) = some x
    exact dyadicCeiling_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicCeilingToEventFlow_injective heq)

instance dyadicCeilingFieldFaithful : FieldFaithful DyadicCeilingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun packet =>
    match packet with
    | DyadicCeilingUp.mk x k c p l u M R E H T P N => [x, k, c, p, l, u, M, R, E, H, T, P, N]
  field_faithful := by
    intro a b hfields
    cases a with
    | mk x1 k1 c1 p1 l1 u1 M1 R1 E1 H1 T1 P1 N1 =>
        cases b with
        | mk x2 k2 c2 p2 l2 u2 M2 R2 E2 H2 T2 P2 N2 =>
            injection hfields with hx t1
            cases hx
            injection t1 with hk t2
            cases hk
            injection t2 with hc t3
            cases hc
            injection t3 with hp t4
            cases hp
            injection t4 with hl t5
            cases hl
            injection t5 with hu t6
            cases hu
            injection t6 with hM t7
            cases hM
            injection t7 with hR t8
            cases hR
            injection t8 with hE t9
            cases hE
            injection t9 with hH t10
            cases hH
            injection t10 with hT t11
            cases hT
            injection t11 with hP t12
            cases hP
            injection t12 with hN _
            cases hN
            rfl

namespace TasteGate

theorem DyadicCeilingTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicCeilingDecodeBHist (dyadicCeilingEncodeBHist h) = h) ∧
      (∀ x : DyadicCeilingUp,
        dyadicCeilingFromEventFlow (dyadicCeilingToEventFlow x) = some x) ∧
        (∀ x y : DyadicCeilingUp,
          dyadicCeilingToEventFlow x = dyadicCeilingToEventFlow y → x = y) ∧
          dyadicCeilingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicCeiling_decode_encode_bhist
  · constructor
    · exact dyadicCeiling_round_trip
    · constructor
      · intro x y heq
        exact dyadicCeilingToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.DyadicCeilingUp
