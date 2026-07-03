import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularRealSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularRealSealUp : Type where
  | mk (window regular dyadic modulus endpoint transport continuation provenance localName : BHist) :
      BishopRegularRealSealUp
  deriving DecidableEq

def bishopRegularRealSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularRealSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularRealSealEncodeBHist h

def bishopRegularRealSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularRealSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularRealSealDecodeBHist tail)

private theorem bishopRegularRealSealDecode_encode_bhist :
    ∀ h : BHist, bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularRealSealFields : BishopRegularRealSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealSealUp.mk window regular dyadic modulus endpoint transport continuation
      provenance localName =>
      [window, regular, dyadic, modulus, endpoint, transport, continuation, provenance,
        localName]

def bishopRegularRealSealToEventFlow : BishopRegularRealSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealSealUp.mk window regular dyadic modulus endpoint transport continuation
      provenance localName =>
      [[BMark.b0],
        bishopRegularRealSealEncodeBHist window,
        [BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopRegularRealSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist localName]

def bishopRegularRealSealFromEventFlow : EventFlow → Option BishopRegularRealSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | regular :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | modulus :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | endpoint :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BishopRegularRealSealUp.mk
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    window)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    regular)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    dyadic)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    modulus)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    endpoint)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    transport)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    continuation)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    provenance)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem bishopRegularRealSeal_round_trip :
    ∀ x : BishopRegularRealSealUp,
      bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window regular dyadic modulus endpoint transport continuation provenance localName =>
      change
        some
          (BishopRegularRealSealUp.mk
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist window))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist regular))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist dyadic))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist modulus))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist endpoint))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist transport))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist continuation))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist provenance))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist localName))) =
          some
            (BishopRegularRealSealUp.mk window regular dyadic modulus endpoint transport
              continuation provenance localName)
      rw [bishopRegularRealSealDecode_encode_bhist window,
        bishopRegularRealSealDecode_encode_bhist regular,
        bishopRegularRealSealDecode_encode_bhist dyadic,
        bishopRegularRealSealDecode_encode_bhist modulus,
        bishopRegularRealSealDecode_encode_bhist endpoint,
        bishopRegularRealSealDecode_encode_bhist transport,
        bishopRegularRealSealDecode_encode_bhist continuation,
        bishopRegularRealSealDecode_encode_bhist provenance,
        bishopRegularRealSealDecode_encode_bhist localName]

private theorem bishopRegularRealSealToEventFlow_injective {x y : BishopRegularRealSealUp} :
    bishopRegularRealSealToEventFlow x = bishopRegularRealSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) =
        bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow y) :=
    congrArg bishopRegularRealSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRegularRealSeal_round_trip x).symm
      (Eq.trans hread (bishopRegularRealSeal_round_trip y)))

private theorem bishopRegularRealSeal_field_faithful :
    ∀ x y : BishopRegularRealSealUp,
      bishopRegularRealSealFields x = bishopRegularRealSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 G1 D1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 G2 D2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopRegularRealSealBHistCarrier : BHistCarrier BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularRealSealToEventFlow
  fromEventFlow := bishopRegularRealSealFromEventFlow

instance bishopRegularRealSealChapterTasteGate : ChapterTasteGate BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x
    exact bishopRegularRealSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularRealSealToEventFlow_injective heq)

instance bishopRegularRealSealFieldFaithful : FieldFaithful BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRegularRealSealFields
  field_faithful := bishopRegularRealSeal_field_faithful

instance bishopRegularRealSealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularRealSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularRealSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopRegularRealSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist h) = h) ∧
      (∀ x : BishopRegularRealSealUp,
        bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x) ∧
        (∀ x y : BishopRegularRealSealUp,
          bishopRegularRealSealToEventFlow x = bishopRegularRealSealToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful BishopRegularRealSealUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopRegularRealSealUp) ∧
              bishopRegularRealSealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨bishopRegularRealSealDecode_encode_bhist,
      bishopRegularRealSeal_round_trip,
      (fun _ _ heq => bishopRegularRealSealToEventFlow_injective heq),
      ⟨bishopRegularRealSealFieldFaithful⟩,
      ⟨bishopRegularRealSealNontrivial⟩,
      rfl⟩

theorem BishopRegularRealSealNameCertObligations (x : BishopRegularRealSealUp) :
    ∃ W G D M E H C P N : BHist,
      x = BishopRegularRealSealUp.mk W G D M E H C P N ∧
        bishopRegularRealSealFields x = [W, G, D, M, E, H, C, P, N] ∧
          bishopRegularRealSealToEventFlow x =
            [[BMark.b0],
              bishopRegularRealSealEncodeBHist W,
              [BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist G,
              [BMark.b1, BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist D,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist M,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist E,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist H,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              bishopRegularRealSealEncodeBHist C,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist P,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              bishopRegularRealSealEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W G D M E H C P N =>
      exact ⟨W, G, D, M, E, H, C, P, N, rfl, rfl, rfl⟩

namespace TasteGate

abbrev BishopRegularRealSealUp := BEDC.Derived.BishopRegularRealSealUp.BishopRegularRealSealUp

end TasteGate

end BEDC.Derived.BishopRegularRealSealUp
