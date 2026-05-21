import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalDensityRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalDensityRealUp : Type where
  | mk : (L U WL WU A I Q T R H C P N : BHist) → RationalDensityRealUp
  deriving DecidableEq

def rationalDensityRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalDensityRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalDensityRealEncodeBHist h

def rationalDensityRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalDensityRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalDensityRealDecodeBHist tail)

private theorem rationalDensityRealDecode_encode_bhist :
    ∀ h : BHist,
      rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalDensityRealToEventFlow : RationalDensityRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RationalDensityRealUp.mk L U WL WU A I Q T R H C P N =>
      [[BMark.b0],
        rationalDensityRealEncodeBHist L,
        [BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist WL,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist WU,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        rationalDensityRealEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rationalDensityRealEncodeBHist N]

def rationalDensityRealFromEventFlow :
    EventFlow → Option RationalDensityRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: rest0 =>
      match rest0 with
      | L :: rest1 =>
          match rest1 with
          | _tag1 :: rest2 =>
              match rest2 with
              | U :: rest3 =>
                  match rest3 with
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | WL :: rest5 =>
                          match rest5 with
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | WU :: rest7 =>
                                  match rest7 with
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | A :: rest9 =>
                                          match rest9 with
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | I :: rest11 =>
                                                  match rest11 with
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | Q :: rest13 =>
                                                          match rest13 with
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | T :: rest15 =>
                                                                  match rest15 with
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | R :: rest17 =>
                                                                          match rest17 with
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | H :: rest19 =>
                                                                                  match rest19 with
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | C :: rest21 =>
                                                                                          match rest21 with
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | P :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | N :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (RationalDensityRealUp.mk
                                                                                                                  (rationalDensityRealDecodeBHist L)
                                                                                                                  (rationalDensityRealDecodeBHist U)
                                                                                                                  (rationalDensityRealDecodeBHist WL)
                                                                                                                  (rationalDensityRealDecodeBHist WU)
                                                                                                                  (rationalDensityRealDecodeBHist A)
                                                                                                                  (rationalDensityRealDecodeBHist I)
                                                                                                                  (rationalDensityRealDecodeBHist Q)
                                                                                                                  (rationalDensityRealDecodeBHist T)
                                                                                                                  (rationalDensityRealDecodeBHist R)
                                                                                                                  (rationalDensityRealDecodeBHist H)
                                                                                                                  (rationalDensityRealDecodeBHist C)
                                                                                                                  (rationalDensityRealDecodeBHist P)
                                                                                                                  (rationalDensityRealDecodeBHist N))
                                                                                                          | _ :: _ => none
                                                                                                      | [] => none
                                                                                                  | [] => none
                                                                                              | [] => none
                                                                                          | [] => none
                                                                                      | [] => none
                                                                                  | [] => none
                                                                              | [] => none
                                                                          | [] => none
                                                                      | [] => none
                                                                  | [] => none
                                                              | [] => none
                                                          | [] => none
                                                      | [] => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def rationalDensityRealFields :
    RationalDensityRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalDensityRealUp.mk L U WL WU A I Q T R H C P N =>
      [L, U, WL, WU, A, I, Q, T, R, H, C, P, N]

private theorem rationalDensityReal_round_trip :
    ∀ x : RationalDensityRealUp,
      rationalDensityRealFromEventFlow
        (rationalDensityRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U WL WU A I Q T R H C P N =>
      change
        some
          (RationalDensityRealUp.mk
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist L))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist U))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist WL))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist WU))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist A))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist I))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist Q))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist T))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist R))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist H))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist C))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist P))
            (rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist N))) =
          some (RationalDensityRealUp.mk L U WL WU A I Q T R H C P N)
      rw [rationalDensityRealDecode_encode_bhist L,
        rationalDensityRealDecode_encode_bhist U,
        rationalDensityRealDecode_encode_bhist WL,
        rationalDensityRealDecode_encode_bhist WU,
        rationalDensityRealDecode_encode_bhist A,
        rationalDensityRealDecode_encode_bhist I,
        rationalDensityRealDecode_encode_bhist Q,
        rationalDensityRealDecode_encode_bhist T,
        rationalDensityRealDecode_encode_bhist R,
        rationalDensityRealDecode_encode_bhist H,
        rationalDensityRealDecode_encode_bhist C,
        rationalDensityRealDecode_encode_bhist P,
        rationalDensityRealDecode_encode_bhist N]

private theorem rationalDensityRealToEventFlow_injective
    {x y : RationalDensityRealUp} :
    rationalDensityRealToEventFlow x =
      rationalDensityRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalDensityRealFromEventFlow (rationalDensityRealToEventFlow x) =
        rationalDensityRealFromEventFlow (rationalDensityRealToEventFlow y) :=
    congrArg rationalDensityRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalDensityReal_round_trip x).symm
      (Eq.trans hread (rationalDensityReal_round_trip y)))

private theorem rationalDensityRealFields_faithful :
    ∀ x y : RationalDensityRealUp,
      rationalDensityRealFields x = rationalDensityRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk L1 U1 WL1 WU1 A1 I1 Q1 T1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 WL2 WU2 A2 I2 Q2 T2 R2 H2 C2 P2 N2 =>
          cases h
          rfl

instance rationalDensityRealBHistCarrier :
    BHistCarrier RationalDensityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalDensityRealToEventFlow
  fromEventFlow := rationalDensityRealFromEventFlow

instance rationalDensityRealChapterTasteGate :
    ChapterTasteGate RationalDensityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalDensityRealFromEventFlow
        (rationalDensityRealToEventFlow x) = some x
    exact rationalDensityReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalDensityRealToEventFlow_injective heq)

instance rationalDensityRealFieldFaithful :
    FieldFaithful RationalDensityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalDensityRealFields
  field_faithful := rationalDensityRealFields_faithful

instance rationalDensityRealNontrivial :
    Nontrivial RationalDensityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalDensityRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RationalDensityRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RationalDensityRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RationalDensityRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalDensityRealDecodeBHist (rationalDensityRealEncodeBHist h) = h) ∧
      (∀ x : RationalDensityRealUp,
        rationalDensityRealFromEventFlow (rationalDensityRealToEventFlow x) =
          some x) ∧
        (∀ x y : RationalDensityRealUp,
          rationalDensityRealToEventFlow x =
            rationalDensityRealToEventFlow y → x = y) ∧
          rationalDensityRealEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RationalDensityRealUp,
              rationalDensityRealFields x = rationalDensityRealFields y → x = y) ∧
              (∃ x y : RationalDensityRealUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact rationalDensityRealDecode_encode_bhist
  · constructor
    · exact rationalDensityReal_round_trip
    · constructor
      · intro x y heq
        exact rationalDensityRealToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact rationalDensityRealFields_faithful
          · exact
              ⟨RationalDensityRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                RationalDensityRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.RationalDensityRealUp
