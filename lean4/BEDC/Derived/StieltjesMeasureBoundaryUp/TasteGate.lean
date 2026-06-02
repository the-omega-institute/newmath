import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StieltjesMeasureBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StieltjesMeasureBoundaryUp : Type where
  | mk (B Pi J R E H C P N : BHist) : StieltjesMeasureBoundaryUp
  deriving DecidableEq

def stieltjesMeasureBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stieltjesMeasureBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stieltjesMeasureBoundaryEncodeBHist h

def stieltjesMeasureBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stieltjesMeasureBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stieltjesMeasureBoundaryDecodeBHist tail)

private theorem stieltjesMeasureBoundary_decode_encode_bhist :
    forall h : BHist,
      stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem stieltjesMeasureBoundary_mk_congr
    {B B' Pi Pi' J J' R R' E E' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hPi : Pi' = Pi) (hJ : J' = J) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    StieltjesMeasureBoundaryUp.mk B' Pi' J' R' E' H' C' P' N' =
      StieltjesMeasureBoundaryUp.mk B Pi J R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hPi
  cases hJ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def stieltjesMeasureBoundaryFields : StieltjesMeasureBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StieltjesMeasureBoundaryUp.mk B Pi J R E H C P N => [B, Pi, J, R, E, H, C, P, N]

def stieltjesMeasureBoundaryToEventFlow : StieltjesMeasureBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (stieltjesMeasureBoundaryFields x).map stieltjesMeasureBoundaryEncodeBHist

private def stieltjesMeasureBoundaryRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => stieltjesMeasureBoundaryRawAt n rest

private def stieltjesMeasureBoundaryLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => stieltjesMeasureBoundaryLengthEq n rest

def stieltjesMeasureBoundaryFromEventFlow : EventFlow -> Option StieltjesMeasureBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match stieltjesMeasureBoundaryLengthEq 9 flow with
      | true =>
          some
            (StieltjesMeasureBoundaryUp.mk
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 0 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 1 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 2 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 3 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 4 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 5 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 6 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 7 flow))
              (stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryRawAt 8 flow)))
      | false => none

private theorem stieltjesMeasureBoundary_round_trip :
    forall x : StieltjesMeasureBoundaryUp,
      stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Pi J R E H C P N =>
      exact
        congrArg some
          (stieltjesMeasureBoundary_mk_congr
            (stieltjesMeasureBoundary_decode_encode_bhist B)
            (stieltjesMeasureBoundary_decode_encode_bhist Pi)
            (stieltjesMeasureBoundary_decode_encode_bhist J)
            (stieltjesMeasureBoundary_decode_encode_bhist R)
            (stieltjesMeasureBoundary_decode_encode_bhist E)
            (stieltjesMeasureBoundary_decode_encode_bhist H)
            (stieltjesMeasureBoundary_decode_encode_bhist C)
            (stieltjesMeasureBoundary_decode_encode_bhist P)
            (stieltjesMeasureBoundary_decode_encode_bhist N))

private theorem stieltjesMeasureBoundaryToEventFlow_injective
    {x y : StieltjesMeasureBoundaryUp} :
    stieltjesMeasureBoundaryToEventFlow x = stieltjesMeasureBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) =
        stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow y) :=
    congrArg stieltjesMeasureBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stieltjesMeasureBoundary_round_trip x).symm
      (Eq.trans hread (stieltjesMeasureBoundary_round_trip y)))

instance stieltjesMeasureBoundaryBHistCarrier : BHistCarrier StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stieltjesMeasureBoundaryToEventFlow
  fromEventFlow := stieltjesMeasureBoundaryFromEventFlow

instance stieltjesMeasureBoundaryChapterTasteGate :
    ChapterTasteGate StieltjesMeasureBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) = some x
    exact stieltjesMeasureBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stieltjesMeasureBoundaryToEventFlow_injective heq)

theorem StieltjesMeasureBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      stieltjesMeasureBoundaryDecodeBHist (stieltjesMeasureBoundaryEncodeBHist h) = h) ∧
      (forall x : StieltjesMeasureBoundaryUp,
        stieltjesMeasureBoundaryFromEventFlow (stieltjesMeasureBoundaryToEventFlow x) = some x) ∧
        (forall x y : StieltjesMeasureBoundaryUp,
          stieltjesMeasureBoundaryToEventFlow x = stieltjesMeasureBoundaryToEventFlow y ->
            x = y) ∧
          stieltjesMeasureBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨stieltjesMeasureBoundary_decode_encode_bhist,
      stieltjesMeasureBoundary_round_trip,
      (fun _ _ heq => stieltjesMeasureBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StieltjesMeasureBoundaryUp
