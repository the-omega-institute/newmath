import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompactIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompactIntervalUp : Type where
  | mk (I L F W R D E H C P N : BHist) : BishopCompactIntervalUp
  deriving DecidableEq

def bishopCompactIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompactIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompactIntervalEncodeBHist h

def bishopCompactIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompactIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompactIntervalDecodeBHist tail)

private theorem bishopCompactInterval_decode_encode_bhist :
    ∀ h : BHist, bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompactIntervalFields : BishopCompactIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompactIntervalUp.mk I L F W R D E H C P N => [I, L, F, W, R, D, E, H, C, P, N]

def bishopCompactIntervalToEventFlow : BishopCompactIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompactIntervalUp.mk I L F W R D E H C P N =>
      [bishopCompactIntervalEncodeBHist I,
        bishopCompactIntervalEncodeBHist L,
        bishopCompactIntervalEncodeBHist F,
        bishopCompactIntervalEncodeBHist W,
        bishopCompactIntervalEncodeBHist R,
        bishopCompactIntervalEncodeBHist D,
        bishopCompactIntervalEncodeBHist E,
        bishopCompactIntervalEncodeBHist H,
        bishopCompactIntervalEncodeBHist C,
        bishopCompactIntervalEncodeBHist P,
        bishopCompactIntervalEncodeBHist N]

def bishopCompactIntervalFromEventFlow : EventFlow → Option BishopCompactIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: restL =>
      match restL with
      | [] => none
      | L :: restF =>
          match restF with
          | [] => none
          | F :: restW =>
              match restW with
              | [] => none
              | W :: restR =>
                  match restR with
                  | [] => none
                  | R :: restD =>
                      match restD with
                      | [] => none
                      | D :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (BishopCompactIntervalUp.mk
                                                      (bishopCompactIntervalDecodeBHist I)
                                                      (bishopCompactIntervalDecodeBHist L)
                                                      (bishopCompactIntervalDecodeBHist F)
                                                      (bishopCompactIntervalDecodeBHist W)
                                                      (bishopCompactIntervalDecodeBHist R)
                                                      (bishopCompactIntervalDecodeBHist D)
                                                      (bishopCompactIntervalDecodeBHist E)
                                                      (bishopCompactIntervalDecodeBHist H)
                                                      (bishopCompactIntervalDecodeBHist C)
                                                      (bishopCompactIntervalDecodeBHist P)
                                                      (bishopCompactIntervalDecodeBHist N))
                                              | _ :: _ => none

private theorem bishopCompactInterval_round_trip :
    ∀ x : BishopCompactIntervalUp,
      bishopCompactIntervalFromEventFlow (bishopCompactIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L F W R D E H C P N =>
      change
        some
          (BishopCompactIntervalUp.mk
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist I))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist L))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist F))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist W))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist R))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist D))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist E))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist H))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist C))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist P))
            (bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist N))) =
          some (BishopCompactIntervalUp.mk I L F W R D E H C P N)
      rw [bishopCompactInterval_decode_encode_bhist I,
        bishopCompactInterval_decode_encode_bhist L,
        bishopCompactInterval_decode_encode_bhist F,
        bishopCompactInterval_decode_encode_bhist W,
        bishopCompactInterval_decode_encode_bhist R,
        bishopCompactInterval_decode_encode_bhist D,
        bishopCompactInterval_decode_encode_bhist E,
        bishopCompactInterval_decode_encode_bhist H,
        bishopCompactInterval_decode_encode_bhist C,
        bishopCompactInterval_decode_encode_bhist P,
        bishopCompactInterval_decode_encode_bhist N]

private theorem bishopCompactIntervalToEventFlow_injective {x y : BishopCompactIntervalUp} :
    bishopCompactIntervalToEventFlow x = bishopCompactIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompactIntervalFromEventFlow (bishopCompactIntervalToEventFlow x) =
        bishopCompactIntervalFromEventFlow (bishopCompactIntervalToEventFlow y) :=
    congrArg bishopCompactIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompactInterval_round_trip x).symm
      (Eq.trans hread (bishopCompactInterval_round_trip y)))

private theorem bishopCompactInterval_field_faithful :
    ∀ x y : BishopCompactIntervalUp,
      bishopCompactIntervalFields x = bishopCompactIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 L1 F1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 L2 F2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance bishopCompactIntervalBHistCarrier : BHistCarrier BishopCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompactIntervalToEventFlow
  fromEventFlow := bishopCompactIntervalFromEventFlow

instance bishopCompactIntervalChapterTasteGate : ChapterTasteGate BishopCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompactIntervalFromEventFlow (bishopCompactIntervalToEventFlow x) = some x
    exact bishopCompactInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompactIntervalToEventFlow_injective heq)

instance bishopCompactIntervalFieldFaithful : FieldFaithful BishopCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCompactIntervalFields
  field_faithful := bishopCompactInterval_field_faithful

instance bishopCompactIntervalNontrivial : Nontrivial BishopCompactIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCompactIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCompactIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopCompactIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompactIntervalChapterTasteGate

theorem BishopCompactIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCompactIntervalDecodeBHist (bishopCompactIntervalEncodeBHist h) = h) ∧
      (∀ x : BishopCompactIntervalUp,
        bishopCompactIntervalFromEventFlow (bishopCompactIntervalToEventFlow x) = some x) ∧
        (∀ x y : BishopCompactIntervalUp,
          bishopCompactIntervalToEventFlow x = bishopCompactIntervalToEventFlow y → x = y) ∧
          bishopCompactIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨bishopCompactInterval_decode_encode_bhist,
      bishopCompactInterval_round_trip,
      by
        intro x y heq
        exact bishopCompactIntervalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BishopCompactIntervalUp
