import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchauderFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchauderFixedPointUp : Type where
  | mk (K Q V A F E R L H C P N : BHist) : SchauderFixedPointUp
  deriving DecidableEq

def schauderFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schauderFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schauderFixedPointEncodeBHist h

def schauderFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schauderFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schauderFixedPointDecodeBHist tail)

private theorem schauderFixedPoint_decode_encode_bhist :
    ∀ h : BHist, schauderFixedPointDecodeBHist (schauderFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem schauderFixedPoint_mk_congr
    {K K' Q Q' V V' A A' F F' E E' R R' L L' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hQ : Q' = Q) (hV : V' = V) (hA : A' = A)
    (hF : F' = F) (hE : E' = E) (hR : R' = R) (hL : L' = L)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    SchauderFixedPointUp.mk K' Q' V' A' F' E' R' L' H' C' P' N' =
      SchauderFixedPointUp.mk K Q V A F E R L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hQ
  cases hV
  cases hA
  cases hF
  cases hE
  cases hR
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def schauderFixedPointFields : SchauderFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchauderFixedPointUp.mk K Q V A F E R L H C P N => [K, Q, V, A, F, E, R, L, H, C, P, N]

def schauderFixedPointToEventFlow : SchauderFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (schauderFixedPointFields x).map schauderFixedPointEncodeBHist

private def schauderFixedPointRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => schauderFixedPointRawAt n rest

private def schauderFixedPointLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => schauderFixedPointLengthEq n rest

def schauderFixedPointFromEventFlow : EventFlow → Option SchauderFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match schauderFixedPointLengthEq 12 flow with
      | true =>
          some
            (SchauderFixedPointUp.mk
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 0 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 1 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 2 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 3 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 4 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 5 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 6 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 7 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 8 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 9 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 10 flow))
              (schauderFixedPointDecodeBHist (schauderFixedPointRawAt 11 flow)))
      | false => none

private theorem schauderFixedPoint_round_trip :
    ∀ x : SchauderFixedPointUp,
      schauderFixedPointFromEventFlow (schauderFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K Q V A F E R L H C P N =>
      exact
        congrArg some
          (schauderFixedPoint_mk_congr
            (schauderFixedPoint_decode_encode_bhist K)
            (schauderFixedPoint_decode_encode_bhist Q)
            (schauderFixedPoint_decode_encode_bhist V)
            (schauderFixedPoint_decode_encode_bhist A)
            (schauderFixedPoint_decode_encode_bhist F)
            (schauderFixedPoint_decode_encode_bhist E)
            (schauderFixedPoint_decode_encode_bhist R)
            (schauderFixedPoint_decode_encode_bhist L)
            (schauderFixedPoint_decode_encode_bhist H)
            (schauderFixedPoint_decode_encode_bhist C)
            (schauderFixedPoint_decode_encode_bhist P)
            (schauderFixedPoint_decode_encode_bhist N))

private theorem schauderFixedPointToEventFlow_injective {x y : SchauderFixedPointUp} :
    schauderFixedPointToEventFlow x = schauderFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schauderFixedPointFromEventFlow (schauderFixedPointToEventFlow x) =
        schauderFixedPointFromEventFlow (schauderFixedPointToEventFlow y) :=
    congrArg schauderFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (schauderFixedPoint_round_trip x).symm
      (Eq.trans hread (schauderFixedPoint_round_trip y)))

instance schauderFixedPointBHistCarrier : BHistCarrier SchauderFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schauderFixedPointToEventFlow
  fromEventFlow := schauderFixedPointFromEventFlow

instance schauderFixedPointChapterTasteGate : ChapterTasteGate SchauderFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schauderFixedPointFromEventFlow (schauderFixedPointToEventFlow x) = some x
    exact schauderFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (schauderFixedPointToEventFlow_injective heq)

theorem SchauderFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, schauderFixedPointDecodeBHist (schauderFixedPointEncodeBHist h) = h) ∧
      schauderFixedPointFields
          (SchauderFixedPointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        Nonempty (ChapterTasteGate SchauderFixedPointUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨schauderFixedPoint_decode_encode_bhist, rfl,
      Nonempty.intro schauderFixedPointChapterTasteGate⟩

end BEDC.Derived.SchauderFixedPointUp
