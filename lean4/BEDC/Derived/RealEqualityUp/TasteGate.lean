import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealEqualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealEqualityUp : Type where
  | mk (X Y SX SY RX RY W D U C H K P N : BHist) : RealEqualityUp
  deriving DecidableEq

def realEqualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realEqualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realEqualityEncodeBHist h

def realEqualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realEqualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realEqualityDecodeBHist tail)

private theorem realEqualityDecode_encode_bhist :
    ∀ h : BHist, realEqualityDecodeBHist (realEqualityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realEqualityFields : RealEqualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealEqualityUp.mk X Y SX SY RX RY W D U C H K P N =>
      [X, Y, SX, SY, RX, RY, W, D, U, C, H, K, P, N]

def realEqualityToEventFlow : RealEqualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realEqualityFields x).map realEqualityEncodeBHist

def realEqualityFromEventFlow : EventFlow → Option RealEqualityUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | SX :: restSX =>
              match restSX with
              | SY :: restSY =>
                  match restSY with
                  | RX :: restRX =>
                      match restRX with
                      | RY :: restRY =>
                          match restRY with
                          | W :: restW =>
                              match restW with
                              | D :: restD =>
                                  match restD with
                                  | U :: restU =>
                                      match restU with
                                      | C :: restC =>
                                          match restC with
                                          | H :: restH =>
                                              match restH with
                                              | K :: restK =>
                                                  match restK with
                                                  | P :: restP =>
                                                      match restP with
                                                      | N :: rest =>
                                                          match rest with
                                                          | [] =>
                                                              some
                                                                (RealEqualityUp.mk
                                                                  (realEqualityDecodeBHist X)
                                                                  (realEqualityDecodeBHist Y)
                                                                  (realEqualityDecodeBHist SX)
                                                                  (realEqualityDecodeBHist SY)
                                                                  (realEqualityDecodeBHist RX)
                                                                  (realEqualityDecodeBHist RY)
                                                                  (realEqualityDecodeBHist W)
                                                                  (realEqualityDecodeBHist D)
                                                                  (realEqualityDecodeBHist U)
                                                                  (realEqualityDecodeBHist C)
                                                                  (realEqualityDecodeBHist H)
                                                                  (realEqualityDecodeBHist K)
                                                                  (realEqualityDecodeBHist P)
                                                                  (realEqualityDecodeBHist N))
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

private theorem realEquality_round_trip :
    ∀ x : RealEqualityUp, realEqualityFromEventFlow (realEqualityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y SX SY RX RY W D U C H K P N =>
      change
        some
          (RealEqualityUp.mk
            (realEqualityDecodeBHist (realEqualityEncodeBHist X))
            (realEqualityDecodeBHist (realEqualityEncodeBHist Y))
            (realEqualityDecodeBHist (realEqualityEncodeBHist SX))
            (realEqualityDecodeBHist (realEqualityEncodeBHist SY))
            (realEqualityDecodeBHist (realEqualityEncodeBHist RX))
            (realEqualityDecodeBHist (realEqualityEncodeBHist RY))
            (realEqualityDecodeBHist (realEqualityEncodeBHist W))
            (realEqualityDecodeBHist (realEqualityEncodeBHist D))
            (realEqualityDecodeBHist (realEqualityEncodeBHist U))
            (realEqualityDecodeBHist (realEqualityEncodeBHist C))
            (realEqualityDecodeBHist (realEqualityEncodeBHist H))
            (realEqualityDecodeBHist (realEqualityEncodeBHist K))
            (realEqualityDecodeBHist (realEqualityEncodeBHist P))
            (realEqualityDecodeBHist (realEqualityEncodeBHist N))) =
          some (RealEqualityUp.mk X Y SX SY RX RY W D U C H K P N)
      rw [realEqualityDecode_encode_bhist X,
        realEqualityDecode_encode_bhist Y,
        realEqualityDecode_encode_bhist SX,
        realEqualityDecode_encode_bhist SY,
        realEqualityDecode_encode_bhist RX,
        realEqualityDecode_encode_bhist RY,
        realEqualityDecode_encode_bhist W,
        realEqualityDecode_encode_bhist D,
        realEqualityDecode_encode_bhist U,
        realEqualityDecode_encode_bhist C,
        realEqualityDecode_encode_bhist H,
        realEqualityDecode_encode_bhist K,
        realEqualityDecode_encode_bhist P,
        realEqualityDecode_encode_bhist N]

private theorem realEqualityToEventFlow_injective {x y : RealEqualityUp} :
    realEqualityToEventFlow x = realEqualityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realEqualityFromEventFlow (realEqualityToEventFlow x) =
        realEqualityFromEventFlow (realEqualityToEventFlow y) :=
    congrArg realEqualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realEquality_round_trip x).symm (Eq.trans hread (realEquality_round_trip y)))

private theorem realEquality_field_faithful :
    ∀ x y : RealEqualityUp, realEqualityFields x = realEqualityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 SX1 SY1 RX1 RY1 W1 D1 U1 C1 H1 K1 P1 N1 =>
      cases y with
      | mk X2 Y2 SX2 SY2 RX2 RY2 W2 D2 U2 C2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance realEqualityBHistCarrier : BHistCarrier RealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realEqualityToEventFlow
  fromEventFlow := realEqualityFromEventFlow

instance realEqualityChapterTasteGate : ChapterTasteGate RealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realEqualityFromEventFlow (realEqualityToEventFlow x) = some x
    exact realEquality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realEqualityToEventFlow_injective heq)

instance realEqualityFieldFaithful : FieldFaithful RealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realEqualityFields
  field_faithful := realEquality_field_faithful

instance realEqualityNontrivial : BEDC.Meta.TasteGate.Nontrivial RealEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealEqualityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealEqualityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealEqualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realEqualityChapterTasteGate

theorem RealEqualityTasteGate_single_carrier_alignment :
    (∀ h : BHist, realEqualityDecodeBHist (realEqualityEncodeBHist h) = h) ∧
      (∀ x : RealEqualityUp,
        realEqualityFromEventFlow (realEqualityToEventFlow x) = some x) ∧
        (∀ x y : RealEqualityUp,
          realEqualityToEventFlow x = realEqualityToEventFlow y → x = y) ∧
          realEqualityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨realEqualityDecode_encode_bhist,
      realEquality_round_trip,
      (fun _ _ heq => realEqualityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealEqualityUp
