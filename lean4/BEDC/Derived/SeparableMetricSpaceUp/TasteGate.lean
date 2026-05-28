import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparableMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparableMetricSpaceUp : Type where
  | mk (M D E W R Q H C P N : BHist) : SeparableMetricSpaceUp
  deriving DecidableEq

def separableMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separableMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separableMetricSpaceEncodeBHist h

def separableMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separableMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separableMetricSpaceDecodeBHist tail)

private theorem SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      separableMetricSpaceDecodeBHist (separableMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem SeparableMetricSpaceTasteGate_single_carrier_alignment_mk_congr
    {M M' D D' E E' W W' R R' Q Q' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hD : D' = D) (hE : E' = E) (hW : W' = W)
    (hR : R' = R) (hQ : Q' = Q) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    SeparableMetricSpaceUp.mk M' D' E' W' R' Q' H' C' P' N' =
      SeparableMetricSpaceUp.mk M D E W R Q H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hD
  cases hE
  cases hW
  cases hR
  cases hQ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def separableMetricSpaceFields : SeparableMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparableMetricSpaceUp.mk M D E W R Q H C P N => [M, D, E, W, R, Q, H, C, P, N]

def separableMetricSpaceToEventFlow : SeparableMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separableMetricSpaceFields x).map separableMetricSpaceEncodeBHist

private def separableMetricSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => separableMetricSpaceRawAt n rest

private def separableMetricSpaceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => separableMetricSpaceLengthEq n rest

def separableMetricSpaceFromEventFlow : EventFlow → Option SeparableMetricSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match separableMetricSpaceLengthEq 10 flow with
      | true =>
          some
            (SeparableMetricSpaceUp.mk
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 0 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 1 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 2 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 3 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 4 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 5 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 6 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 7 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 8 flow))
              (separableMetricSpaceDecodeBHist (separableMetricSpaceRawAt 9 flow)))
      | false => none

private theorem SeparableMetricSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparableMetricSpaceUp,
      separableMetricSpaceFromEventFlow (separableMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D E W R Q H C P N =>
      exact
        congrArg some
          (SeparableMetricSpaceTasteGate_single_carrier_alignment_mk_congr
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode M)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode D)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode E)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode W)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode R)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode Q)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode H)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode C)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode P)
            (SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode N))

private theorem SeparableMetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparableMetricSpaceUp} :
    separableMetricSpaceToEventFlow x = separableMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separableMetricSpaceFromEventFlow (separableMetricSpaceToEventFlow x) =
        separableMetricSpaceFromEventFlow (separableMetricSpaceToEventFlow y) :=
    congrArg separableMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparableMetricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparableMetricSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance separableMetricSpaceBHistCarrier : BHistCarrier SeparableMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separableMetricSpaceToEventFlow
  fromEventFlow := separableMetricSpaceFromEventFlow

instance separableMetricSpaceChapterTasteGate : ChapterTasteGate SeparableMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separableMetricSpaceFromEventFlow (separableMetricSpaceToEventFlow x) = some x
    exact SeparableMetricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparableMetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SeparableMetricSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, separableMetricSpaceDecodeBHist (separableMetricSpaceEncodeBHist h) = h) ∧
      (∀ x : SeparableMetricSpaceUp,
        separableMetricSpaceFromEventFlow (separableMetricSpaceToEventFlow x) = some x) ∧
        (∀ x y : SeparableMetricSpaceUp,
          separableMetricSpaceToEventFlow x = separableMetricSpaceToEventFlow y → x = y) ∧
          separableMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SeparableMetricSpaceTasteGate_single_carrier_alignment_decode_encode,
      SeparableMetricSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        SeparableMetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.SeparableMetricSpaceUp
