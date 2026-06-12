import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealLocatedOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealLocatedOrderUp : Type where
  | mk (B R D S Q A O H C P N : BHist) : BishopRealLocatedOrderUp
  deriving DecidableEq

def bishopRealLocatedOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealLocatedOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealLocatedOrderEncodeBHist h

def bishopRealLocatedOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealLocatedOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealLocatedOrderDecodeBHist tail)

private theorem bishopRealLocatedOrderDecode_encode_bhist :
    ∀ h : BHist,
      bishopRealLocatedOrderDecodeBHist
        (bishopRealLocatedOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealLocatedOrderFields : BishopRealLocatedOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealLocatedOrderUp.mk B R D S Q A O H C P N => [B, R, D, S, Q, A, O, H, C, P, N]

def bishopRealLocatedOrderToEventFlow :
    BishopRealLocatedOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealLocatedOrderFields x).map bishopRealLocatedOrderEncodeBHist

def bishopRealLocatedOrderFromEventFlow :
    EventFlow → Option BishopRealLocatedOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | B :: restR =>
      match restR with
      | [] => none
      | R :: restD =>
          match restD with
          | [] => none
          | D :: restS =>
              match restS with
              | [] => none
              | S :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restA =>
                      match restA with
                      | [] => none
                      | A :: restO =>
                          match restO with
                          | [] => none
                          | O :: restH =>
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
                                                    (BishopRealLocatedOrderUp.mk
                                                      (bishopRealLocatedOrderDecodeBHist B)
                                                      (bishopRealLocatedOrderDecodeBHist R)
                                                      (bishopRealLocatedOrderDecodeBHist D)
                                                      (bishopRealLocatedOrderDecodeBHist S)
                                                      (bishopRealLocatedOrderDecodeBHist Q)
                                                      (bishopRealLocatedOrderDecodeBHist A)
                                                      (bishopRealLocatedOrderDecodeBHist O)
                                                      (bishopRealLocatedOrderDecodeBHist H)
                                                      (bishopRealLocatedOrderDecodeBHist C)
                                                      (bishopRealLocatedOrderDecodeBHist P)
                                                      (bishopRealLocatedOrderDecodeBHist N))
                                              | _ :: _ => none

private theorem bishopRealLocatedOrder_round_trip :
    ∀ x : BishopRealLocatedOrderUp,
      bishopRealLocatedOrderFromEventFlow
        (bishopRealLocatedOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B R D S Q A O H C P N =>
      change
        some
          (BishopRealLocatedOrderUp.mk
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist B))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist R))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist D))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist S))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist Q))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist A))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist O))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist H))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist C))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist P))
            (bishopRealLocatedOrderDecodeBHist (bishopRealLocatedOrderEncodeBHist N))) =
          some (BishopRealLocatedOrderUp.mk B R D S Q A O H C P N)
      rw [bishopRealLocatedOrderDecode_encode_bhist B,
        bishopRealLocatedOrderDecode_encode_bhist R,
        bishopRealLocatedOrderDecode_encode_bhist D,
        bishopRealLocatedOrderDecode_encode_bhist S,
        bishopRealLocatedOrderDecode_encode_bhist Q,
        bishopRealLocatedOrderDecode_encode_bhist A,
        bishopRealLocatedOrderDecode_encode_bhist O,
        bishopRealLocatedOrderDecode_encode_bhist H,
        bishopRealLocatedOrderDecode_encode_bhist C,
        bishopRealLocatedOrderDecode_encode_bhist P,
        bishopRealLocatedOrderDecode_encode_bhist N]

private theorem bishopRealLocatedOrderToEventFlow_injective
    {x y : BishopRealLocatedOrderUp} :
    bishopRealLocatedOrderToEventFlow x =
      bishopRealLocatedOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealLocatedOrderFromEventFlow (bishopRealLocatedOrderToEventFlow x) =
        bishopRealLocatedOrderFromEventFlow (bishopRealLocatedOrderToEventFlow y) :=
    congrArg bishopRealLocatedOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRealLocatedOrder_round_trip x).symm
      (Eq.trans hread (bishopRealLocatedOrder_round_trip y)))

instance bishopRealLocatedOrderBHistCarrier :
    BHistCarrier BishopRealLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealLocatedOrderToEventFlow
  fromEventFlow := bishopRealLocatedOrderFromEventFlow

instance bishopRealLocatedOrderChapterTasteGate :
    ChapterTasteGate BishopRealLocatedOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRealLocatedOrderFromEventFlow
        (bishopRealLocatedOrderToEventFlow x) = some x
    exact bishopRealLocatedOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRealLocatedOrderToEventFlow_injective heq)

theorem BishopRealLocatedOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRealLocatedOrderDecodeBHist
      (bishopRealLocatedOrderEncodeBHist h) = h) ∧
      (∀ x : BishopRealLocatedOrderUp,
        bishopRealLocatedOrderFromEventFlow
          (bishopRealLocatedOrderToEventFlow x) = some x) ∧
        (∀ x y : BishopRealLocatedOrderUp,
          bishopRealLocatedOrderToEventFlow x =
            bishopRealLocatedOrderToEventFlow y -> x = y) ∧
          bishopRealLocatedOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨bishopRealLocatedOrderDecode_encode_bhist,
      bishopRealLocatedOrder_round_trip,
      (fun _ _ heq => bishopRealLocatedOrderToEventFlow_injective heq), rfl⟩

end BEDC.Derived.BishopRealLocatedOrderUp
