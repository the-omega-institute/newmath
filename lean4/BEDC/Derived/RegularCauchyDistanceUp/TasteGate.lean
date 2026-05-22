import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDistanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDistanceUp : Type where
  | mk (X Y S T D Q E H C P N : BHist) : RegularCauchyDistanceUp
  deriving DecidableEq

def regularCauchyDistanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDistanceEncodeBHist h

def regularCauchyDistanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDistanceDecodeBHist tail)

private theorem regularCauchyDistance_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem regularCauchyDistance_mk_congr
    {X X' Y Y' S S' T T' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hS : S' = S) (hT : T' = T)
    (hD : D' = D) (hQ : Q' = Q) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyDistanceUp.mk X' Y' S' T' D' Q' E' H' C' P' N' =
      RegularCauchyDistanceUp.mk X Y S T D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hS
  cases hT
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyDistanceFields : RegularCauchyDistanceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDistanceUp.mk X Y S T D Q E H C P N => [X, Y, S, T, D, Q, E, H, C, P, N]

def regularCauchyDistanceToEventFlow : RegularCauchyDistanceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyDistanceFields x).map regularCauchyDistanceEncodeBHist

private def regularCauchyDistanceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyDistanceRawAt n rest

private def regularCauchyDistanceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyDistanceLengthEq n rest

def regularCauchyDistanceFromEventFlow : EventFlow → Option RegularCauchyDistanceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyDistanceLengthEq 11 flow with
      | true =>
          some
            (RegularCauchyDistanceUp.mk
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 0 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 1 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 2 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 3 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 4 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 5 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 6 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 7 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 8 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 9 flow))
              (regularCauchyDistanceDecodeBHist (regularCauchyDistanceRawAt 10 flow)))
      | false => none

private theorem regularCauchyDistance_round_trip :
    ∀ x : RegularCauchyDistanceUp,
      regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S T D Q E H C P N =>
      exact
        congrArg some
          (regularCauchyDistance_mk_congr
            (regularCauchyDistance_decode_encode_bhist X)
            (regularCauchyDistance_decode_encode_bhist Y)
            (regularCauchyDistance_decode_encode_bhist S)
            (regularCauchyDistance_decode_encode_bhist T)
            (regularCauchyDistance_decode_encode_bhist D)
            (regularCauchyDistance_decode_encode_bhist Q)
            (regularCauchyDistance_decode_encode_bhist E)
            (regularCauchyDistance_decode_encode_bhist H)
            (regularCauchyDistance_decode_encode_bhist C)
            (regularCauchyDistance_decode_encode_bhist P)
            (regularCauchyDistance_decode_encode_bhist N))

private theorem regularCauchyDistanceToEventFlow_injective {x y : RegularCauchyDistanceUp} :
    regularCauchyDistanceToEventFlow x = regularCauchyDistanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) =
        regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow y) :=
    congrArg regularCauchyDistanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDistance_round_trip x).symm
      (Eq.trans hread (regularCauchyDistance_round_trip y)))

instance regularCauchyDistanceBHistCarrier : BHistCarrier RegularCauchyDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDistanceToEventFlow
  fromEventFlow := regularCauchyDistanceFromEventFlow

instance regularCauchyDistanceChapterTasteGate : ChapterTasteGate RegularCauchyDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x
    exact regularCauchyDistance_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDistanceToEventFlow_injective heq)

theorem RegularCauchyDistanceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyDistanceUp,
        regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyDistanceUp,
          regularCauchyDistanceToEventFlow x = regularCauchyDistanceToEventFlow y → x = y) ∧
          regularCauchyDistanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyDistance_decode_encode_bhist,
      regularCauchyDistance_round_trip,
      (fun _ _ heq => regularCauchyDistanceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyDistanceUp
