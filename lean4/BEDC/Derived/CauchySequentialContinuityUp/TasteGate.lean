import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequentialContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequentialContinuityUp : Type where
  | packet (F X Y S C M R H K P N : BHist) : CauchySequentialContinuityUp
  deriving DecidableEq

private def cauchySequentialContinuityEncodeRow : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequentialContinuityEncodeRow h
  | BHist.e1 h => BMark.b1 :: cauchySequentialContinuityEncodeRow h

private def cauchySequentialContinuityDecodeRow : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequentialContinuityDecodeRow tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequentialContinuityDecodeRow tail)

private theorem CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row :
    ∀ h : BHist,
      cauchySequentialContinuityDecodeRow (cauchySequentialContinuityEncodeRow h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchySequentialContinuityTasteGate_single_carrier_alignment_packet_congr
    {F F' X X' Y Y' S S' C C' M M' R R' H H' K K' P P' N N' : BHist}
    (hF : F' = F) (hX : X' = X) (hY : Y' = Y) (hS : S' = S)
    (hC : C' = C) (hM : M' = M) (hR : R' = R) (hH : H' = H)
    (hK : K' = K) (hP : P' = P) (hN : N' = N) :
    CauchySequentialContinuityUp.packet F' X' Y' S' C' M' R' H' K' P' N' =
      CauchySequentialContinuityUp.packet F X Y S C M R H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hX
  cases hY
  cases hS
  cases hC
  cases hM
  cases hR
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def cauchySequentialContinuityEncodeBHist :
    CauchySequentialContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequentialContinuityUp.packet F X Y S C M R H K P N =>
      [cauchySequentialContinuityEncodeRow F,
        cauchySequentialContinuityEncodeRow X,
        cauchySequentialContinuityEncodeRow Y,
        cauchySequentialContinuityEncodeRow S,
        cauchySequentialContinuityEncodeRow C,
        cauchySequentialContinuityEncodeRow M,
        cauchySequentialContinuityEncodeRow R,
        cauchySequentialContinuityEncodeRow H,
        cauchySequentialContinuityEncodeRow K,
        cauchySequentialContinuityEncodeRow P,
        cauchySequentialContinuityEncodeRow N]

private def cauchySequentialContinuityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchySequentialContinuityRawAt n rest

private def cauchySequentialContinuityLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchySequentialContinuityLengthEq n rest

def cauchySequentialContinuityDecodeBHist :
    EventFlow → Option CauchySequentialContinuityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchySequentialContinuityLengthEq 11 flow with
      | true =>
          some
            (CauchySequentialContinuityUp.packet
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 0 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 1 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 2 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 3 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 4 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 5 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 6 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 7 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 8 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 9 flow))
              (cauchySequentialContinuityDecodeRow (cauchySequentialContinuityRawAt 10 flow)))
      | false => none

private theorem CauchySequentialContinuityTasteGate_single_carrier_alignment_round_trip
    (x : CauchySequentialContinuityUp) :
    cauchySequentialContinuityDecodeBHist (cauchySequentialContinuityEncodeBHist x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet F X Y S C M R H K P N =>
      exact
        congrArg some
          (CauchySequentialContinuityTasteGate_single_carrier_alignment_packet_congr
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row F)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row X)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row Y)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row S)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row C)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row M)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row R)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row H)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row K)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row P)
            (CauchySequentialContinuityTasteGate_single_carrier_alignment_decode_row N))

private theorem CauchySequentialContinuityTasteGate_single_carrier_alignment_injective
    {x y : CauchySequentialContinuityUp} :
    cauchySequentialContinuityEncodeBHist x =
      cauchySequentialContinuityEncodeBHist y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequentialContinuityDecodeBHist (cauchySequentialContinuityEncodeBHist x) =
        cauchySequentialContinuityDecodeBHist (cauchySequentialContinuityEncodeBHist y) :=
    congrArg cauchySequentialContinuityDecodeBHist heq
  exact Option.some.inj
    (Eq.trans
      (CauchySequentialContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySequentialContinuityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySequentialContinuityBHistCarrier :
    BHistCarrier CauchySequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequentialContinuityEncodeBHist
  fromEventFlow := cauchySequentialContinuityDecodeBHist

instance cauchySequentialContinuityChapterTasteGate :
    ChapterTasteGate CauchySequentialContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequentialContinuityDecodeBHist (cauchySequentialContinuityEncodeBHist x) =
        some x
    exact CauchySequentialContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySequentialContinuityTasteGate_single_carrier_alignment_injective heq)

theorem CauchySequentialContinuityTasteGate_single_carrier_alignment :
    (∀ x : CauchySequentialContinuityUp,
        cauchySequentialContinuityDecodeBHist (cauchySequentialContinuityEncodeBHist x) =
          some x) ∧
      (∀ x y : CauchySequentialContinuityUp,
        cauchySequentialContinuityEncodeBHist x =
          cauchySequentialContinuityEncodeBHist y → x = y) ∧
        cauchySequentialContinuityEncodeBHist
            (CauchySequentialContinuityUp.packet
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          ([[], [], [], [], [], [], [], [], [], [], []] : EventFlow) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySequentialContinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchySequentialContinuityTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchySequentialContinuityUp
