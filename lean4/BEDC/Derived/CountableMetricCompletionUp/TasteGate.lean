import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableMetricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableMetricCompletionUp : Type where
  | packet (X M C S R E H K P N : BHist) : CountableMetricCompletionUp
  deriving DecidableEq

private def countableMetricCompletionEncodeRow : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableMetricCompletionEncodeRow h
  | BHist.e1 h => BMark.b1 :: countableMetricCompletionEncodeRow h

private def countableMetricCompletionDecodeRow : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableMetricCompletionDecodeRow tail)
  | BMark.b1 :: tail => BHist.e1 (countableMetricCompletionDecodeRow tail)

private theorem CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row :
    ∀ h : BHist, countableMetricCompletionDecodeRow (countableMetricCompletionEncodeRow h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CountableMetricCompletionTasteGate_single_carrier_alignment_packet_congr
    {X X' M M' C C' S S' R R' E E' H H' K K' P P' N N' : BHist}
    (hX : X' = X) (hM : M' = M) (hC : C' = C) (hS : S' = S)
    (hR : R' = R) (hE : E' = E) (hH : H' = H) (hK : K' = K)
    (hP : P' = P) (hN : N' = N) :
    CountableMetricCompletionUp.packet X' M' C' S' R' E' H' K' P' N' =
      CountableMetricCompletionUp.packet X M C S R E H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hM
  cases hC
  cases hS
  cases hR
  cases hE
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def countableMetricCompletionEncodeBHist : CountableMetricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CountableMetricCompletionUp.packet X M C S R E H K P N =>
      [countableMetricCompletionEncodeRow X,
        countableMetricCompletionEncodeRow M,
        countableMetricCompletionEncodeRow C,
        countableMetricCompletionEncodeRow S,
        countableMetricCompletionEncodeRow R,
        countableMetricCompletionEncodeRow E,
        countableMetricCompletionEncodeRow H,
        countableMetricCompletionEncodeRow K,
        countableMetricCompletionEncodeRow P,
        countableMetricCompletionEncodeRow N]

private def countableMetricCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => countableMetricCompletionRawAt n rest

private def countableMetricCompletionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => countableMetricCompletionLengthEq n rest

def countableMetricCompletionDecodeBHist :
    EventFlow → Option CountableMetricCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match countableMetricCompletionLengthEq 10 flow with
      | true =>
          some
            (CountableMetricCompletionUp.packet
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 0 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 1 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 2 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 3 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 4 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 5 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 6 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 7 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 8 flow))
              (countableMetricCompletionDecodeRow (countableMetricCompletionRawAt 9 flow)))
      | false => none

private theorem CountableMetricCompletionTasteGate_single_carrier_alignment_round_trip
    (x : CountableMetricCompletionUp) :
    countableMetricCompletionDecodeBHist (countableMetricCompletionEncodeBHist x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet X M C S R E H K P N =>
      exact
        congrArg some
          (CountableMetricCompletionTasteGate_single_carrier_alignment_packet_congr
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row X)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row M)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row C)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row S)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row R)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row E)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row H)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row K)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row P)
            (CountableMetricCompletionTasteGate_single_carrier_alignment_decode_row N))

private theorem CountableMetricCompletionTasteGate_single_carrier_alignment_injective
    {x y : CountableMetricCompletionUp} :
    countableMetricCompletionEncodeBHist x =
      countableMetricCompletionEncodeBHist y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableMetricCompletionDecodeBHist (countableMetricCompletionEncodeBHist x) =
        countableMetricCompletionDecodeBHist (countableMetricCompletionEncodeBHist y) :=
    congrArg countableMetricCompletionDecodeBHist heq
  exact Option.some.inj
    (Eq.trans
      (CountableMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CountableMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance countableMetricCompletionBHistCarrier :
    BHistCarrier CountableMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableMetricCompletionEncodeBHist
  fromEventFlow := countableMetricCompletionDecodeBHist

instance countableMetricCompletionChapterTasteGate :
    ChapterTasteGate CountableMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      countableMetricCompletionDecodeBHist (countableMetricCompletionEncodeBHist x) =
        some x
    exact CountableMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CountableMetricCompletionTasteGate_single_carrier_alignment_injective heq)

theorem CountableMetricCompletionTasteGate_single_carrier_alignment :
    (∀ x : CountableMetricCompletionUp,
        countableMetricCompletionDecodeBHist (countableMetricCompletionEncodeBHist x) =
          some x) ∧
      (∀ x y : CountableMetricCompletionUp,
        countableMetricCompletionEncodeBHist x =
          countableMetricCompletionEncodeBHist y → x = y) ∧
        countableMetricCompletionEncodeBHist
            (CountableMetricCompletionUp.packet
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          ([[], [], [], [], [], [], [], [], [], []] : EventFlow) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CountableMetricCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CountableMetricCompletionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CountableMetricCompletionUp
