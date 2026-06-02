import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactSourceTriangleEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactSourceTriangleEstimateUp : Type where
  | mk (K F U E S R L H C P N : BHist) : CompactSourceTriangleEstimateUp
  deriving DecidableEq

def compactSourceTriangleEstimateEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactSourceTriangleEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactSourceTriangleEstimateEncodeBHist h

def compactSourceTriangleEstimateDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactSourceTriangleEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactSourceTriangleEstimateDecodeBHist tail)

private theorem compactSourceTriangleEstimate_decode_encode_bhist :
    forall h : BHist,
      compactSourceTriangleEstimateDecodeBHist
        (compactSourceTriangleEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem compactSourceTriangleEstimate_mk_congr
    {K K' F F' U U' E E' S S' R R' L L' H H' C C' P P' N N' : BHist}
    (hK : K' = K) (hF : F' = F) (hU : U' = U) (hE : E' = E)
    (hS : S' = S) (hR : R' = R) (hL : L' = L) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CompactSourceTriangleEstimateUp.mk K' F' U' E' S' R' L' H' C' P' N' =
      CompactSourceTriangleEstimateUp.mk K F U E S R L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hF
  cases hU
  cases hE
  cases hS
  cases hR
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def compactSourceTriangleEstimateFields : CompactSourceTriangleEstimateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactSourceTriangleEstimateUp.mk K F U E S R L H C P N =>
      [K, F, U, E, S, R, L, H, C, P, N]

def compactSourceTriangleEstimateToEventFlow : CompactSourceTriangleEstimateUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactSourceTriangleEstimateFields x).map compactSourceTriangleEstimateEncodeBHist

private def compactSourceTriangleEstimateRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => compactSourceTriangleEstimateRawAt n rest

private def compactSourceTriangleEstimateLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => compactSourceTriangleEstimateLengthEq n rest

def compactSourceTriangleEstimateFromEventFlow : EventFlow -> Option CompactSourceTriangleEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match compactSourceTriangleEstimateLengthEq 11 flow with
      | true =>
          some
            (CompactSourceTriangleEstimateUp.mk
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 0 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 1 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 2 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 3 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 4 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 5 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 6 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 7 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 8 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 9 flow))
              (compactSourceTriangleEstimateDecodeBHist
                (compactSourceTriangleEstimateRawAt 10 flow)))
      | false => none

private theorem compactSourceTriangleEstimate_round_trip :
    forall x : CompactSourceTriangleEstimateUp,
      compactSourceTriangleEstimateFromEventFlow
        (compactSourceTriangleEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F U E S R L H C P N =>
      exact
        congrArg some
          (compactSourceTriangleEstimate_mk_congr
            (compactSourceTriangleEstimate_decode_encode_bhist K)
            (compactSourceTriangleEstimate_decode_encode_bhist F)
            (compactSourceTriangleEstimate_decode_encode_bhist U)
            (compactSourceTriangleEstimate_decode_encode_bhist E)
            (compactSourceTriangleEstimate_decode_encode_bhist S)
            (compactSourceTriangleEstimate_decode_encode_bhist R)
            (compactSourceTriangleEstimate_decode_encode_bhist L)
            (compactSourceTriangleEstimate_decode_encode_bhist H)
            (compactSourceTriangleEstimate_decode_encode_bhist C)
            (compactSourceTriangleEstimate_decode_encode_bhist P)
            (compactSourceTriangleEstimate_decode_encode_bhist N))

private theorem compactSourceTriangleEstimateToEventFlow_injective
    {x y : CompactSourceTriangleEstimateUp} :
    compactSourceTriangleEstimateToEventFlow x = compactSourceTriangleEstimateToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactSourceTriangleEstimateFromEventFlow (compactSourceTriangleEstimateToEventFlow x) =
        compactSourceTriangleEstimateFromEventFlow (compactSourceTriangleEstimateToEventFlow y) :=
    congrArg compactSourceTriangleEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactSourceTriangleEstimate_round_trip x).symm
      (Eq.trans hread (compactSourceTriangleEstimate_round_trip y)))

instance compactSourceTriangleEstimateBHistCarrier :
    BHistCarrier CompactSourceTriangleEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactSourceTriangleEstimateToEventFlow
  fromEventFlow := compactSourceTriangleEstimateFromEventFlow

instance compactSourceTriangleEstimateChapterTasteGate :
    ChapterTasteGate CompactSourceTriangleEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactSourceTriangleEstimateFromEventFlow
      (compactSourceTriangleEstimateToEventFlow x) = some x
    exact compactSourceTriangleEstimate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactSourceTriangleEstimateToEventFlow_injective heq)

theorem CompactSourceTriangleEstimateTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactSourceTriangleEstimateDecodeBHist
        (compactSourceTriangleEstimateEncodeBHist h) = h) ∧
      (forall x : CompactSourceTriangleEstimateUp,
        compactSourceTriangleEstimateFromEventFlow
          (compactSourceTriangleEstimateToEventFlow x) = some x) ∧
        (forall x y : CompactSourceTriangleEstimateUp,
          compactSourceTriangleEstimateToEventFlow x =
              compactSourceTriangleEstimateToEventFlow y ->
            x = y) ∧
          compactSourceTriangleEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨compactSourceTriangleEstimate_decode_encode_bhist,
      compactSourceTriangleEstimate_round_trip,
      (fun _ _ heq => compactSourceTriangleEstimateToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactSourceTriangleEstimateUp
