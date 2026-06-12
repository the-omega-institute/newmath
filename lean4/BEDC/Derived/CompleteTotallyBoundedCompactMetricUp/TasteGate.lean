import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteTotallyBoundedCompactMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteTotallyBoundedCompactMetricUp : Type where
  | packet (X M T N F D S R H C P L : BHist) : CompleteTotallyBoundedCompactMetricUp
  deriving DecidableEq

private def completeTotallyBoundedCompactMetricEncodeRow : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeTotallyBoundedCompactMetricEncodeRow h
  | BHist.e1 h => BMark.b1 :: completeTotallyBoundedCompactMetricEncodeRow h

private def completeTotallyBoundedCompactMetricDecodeRow : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeTotallyBoundedCompactMetricDecodeRow tail)
  | BMark.b1 :: tail => BHist.e1 (completeTotallyBoundedCompactMetricDecodeRow tail)

private theorem CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row :
    ∀ h : BHist,
      completeTotallyBoundedCompactMetricDecodeRow
        (completeTotallyBoundedCompactMetricEncodeRow h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_packet_congr
    {X X' M M' T T' N N' F F' D D' S S' R R' H H' C C' P P' L L' : BHist}
    (hX : X' = X) (hM : M' = M) (hT : T' = T) (hN : N' = N)
    (hF : F' = F) (hD : D' = D) (hS : S' = S) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hL : L' = L) :
    CompleteTotallyBoundedCompactMetricUp.packet X' M' T' N' F' D' S' R' H' C' P' L' =
      CompleteTotallyBoundedCompactMetricUp.packet X M T N F D S R H C P L := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hM
  cases hT
  cases hN
  cases hF
  cases hD
  cases hS
  cases hR
  cases hH
  cases hC
  cases hP
  cases hL
  rfl

def completeTotallyBoundedCompactMetricEncodeBHist :
    CompleteTotallyBoundedCompactMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteTotallyBoundedCompactMetricUp.packet X M T N F D S R H C P L =>
      [completeTotallyBoundedCompactMetricEncodeRow X,
        completeTotallyBoundedCompactMetricEncodeRow M,
        completeTotallyBoundedCompactMetricEncodeRow T,
        completeTotallyBoundedCompactMetricEncodeRow N,
        completeTotallyBoundedCompactMetricEncodeRow F,
        completeTotallyBoundedCompactMetricEncodeRow D,
        completeTotallyBoundedCompactMetricEncodeRow S,
        completeTotallyBoundedCompactMetricEncodeRow R,
        completeTotallyBoundedCompactMetricEncodeRow H,
        completeTotallyBoundedCompactMetricEncodeRow C,
        completeTotallyBoundedCompactMetricEncodeRow P,
        completeTotallyBoundedCompactMetricEncodeRow L]

private def completeTotallyBoundedCompactMetricRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => completeTotallyBoundedCompactMetricRawAt n rest

private def completeTotallyBoundedCompactMetricLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => completeTotallyBoundedCompactMetricLengthEq n rest

def completeTotallyBoundedCompactMetricDecodeBHist :
    EventFlow → Option CompleteTotallyBoundedCompactMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match completeTotallyBoundedCompactMetricLengthEq 12 flow with
      | true =>
          some
            (CompleteTotallyBoundedCompactMetricUp.packet
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 0 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 1 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 2 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 3 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 4 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 5 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 6 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 7 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 8 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 9 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 10 flow))
              (completeTotallyBoundedCompactMetricDecodeRow
                (completeTotallyBoundedCompactMetricRawAt 11 flow)))
      | false => none

private theorem CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_round_trip
    (x : CompleteTotallyBoundedCompactMetricUp) :
    completeTotallyBoundedCompactMetricDecodeBHist
      (completeTotallyBoundedCompactMetricEncodeBHist x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet X M T N F D S R H C P L =>
      exact
        congrArg some
          (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_packet_congr
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row X)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row M)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row T)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row N)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row F)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row D)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row S)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row R)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row H)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row C)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row P)
            (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_decode_row L))

private theorem CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_injective
    {x y : CompleteTotallyBoundedCompactMetricUp} :
    completeTotallyBoundedCompactMetricEncodeBHist x =
      completeTotallyBoundedCompactMetricEncodeBHist y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeTotallyBoundedCompactMetricDecodeBHist
          (completeTotallyBoundedCompactMetricEncodeBHist x) =
        completeTotallyBoundedCompactMetricDecodeBHist
          (completeTotallyBoundedCompactMetricEncodeBHist y) :=
    congrArg completeTotallyBoundedCompactMetricDecodeBHist heq
  exact Option.some.inj
    (Eq.trans
      (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_round_trip y)))

instance completeTotallyBoundedCompactMetricBHistCarrier :
    BHistCarrier CompleteTotallyBoundedCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeTotallyBoundedCompactMetricEncodeBHist
  fromEventFlow := completeTotallyBoundedCompactMetricDecodeBHist

instance completeTotallyBoundedCompactMetricChapterTasteGate :
    ChapterTasteGate CompleteTotallyBoundedCompactMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completeTotallyBoundedCompactMetricDecodeBHist
        (completeTotallyBoundedCompactMetricEncodeBHist x) = some x
    exact CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_injective heq)

theorem CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment :
    (∀ x : CompleteTotallyBoundedCompactMetricUp,
        completeTotallyBoundedCompactMetricDecodeBHist
          (completeTotallyBoundedCompactMetricEncodeBHist x) = some x) ∧
      (∀ x y : CompleteTotallyBoundedCompactMetricUp,
        completeTotallyBoundedCompactMetricEncodeBHist x =
          completeTotallyBoundedCompactMetricEncodeBHist y → x = y) ∧
        completeTotallyBoundedCompactMetricEncodeBHist
            (CompleteTotallyBoundedCompactMetricUp.packet
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          ([[], [], [], [], [], [], [], [], [], [], [], []] : EventFlow) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompleteTotallyBoundedCompactMetricTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CompleteTotallyBoundedCompactMetricUp
