import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PringsheimConvergenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PringsheimConvergenceUp : Type where
  | mk (X S T M W R D E H C P N : BHist) : PringsheimConvergenceUp
  deriving DecidableEq

def pringsheimConvergenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pringsheimConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pringsheimConvergenceEncodeBHist h

private def pringsheimConvergenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pringsheimConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pringsheimConvergenceDecodeBHist tail)

private theorem PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def pringsheimConvergenceFields : PringsheimConvergenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PringsheimConvergenceUp.mk X S T M W R D E H C P N =>
      [X, S, T, M, W, R, D, E, H, C, P, N]

private def pringsheimConvergenceToEventFlow : PringsheimConvergenceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (pringsheimConvergenceFields x).map pringsheimConvergenceEncodeBHist

private def pringsheimConvergenceRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => pringsheimConvergenceRawAt index rest

private def pringsheimConvergenceFromEventFlow
    (flow : EventFlow) : Option PringsheimConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PringsheimConvergenceUp.mk
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 0 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 1 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 2 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 3 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 4 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 5 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 6 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 7 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 8 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 9 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 10 flow))
      (pringsheimConvergenceDecodeBHist (pringsheimConvergenceRawAt 11 flow)))

private theorem PringsheimConvergenceTasteGate_single_carrier_alignment_round_trip :
    forall x : PringsheimConvergenceUp,
      pringsheimConvergenceFromEventFlow (pringsheimConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S T M W R D E H C P N =>
      change
        some
          (PringsheimConvergenceUp.mk
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist X))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist S))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist T))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist M))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist W))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist R))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist D))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist E))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist H))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist C))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist P))
            (pringsheimConvergenceDecodeBHist (pringsheimConvergenceEncodeBHist N))) =
          some (PringsheimConvergenceUp.mk X S T M W R D E H C P N)
      rw [PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode X,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode T,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode M,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        PringsheimConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem PringsheimConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PringsheimConvergenceUp} :
    pringsheimConvergenceToEventFlow x = pringsheimConvergenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pringsheimConvergenceFromEventFlow (pringsheimConvergenceToEventFlow x) =
        pringsheimConvergenceFromEventFlow (pringsheimConvergenceToEventFlow y) :=
    congrArg pringsheimConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PringsheimConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PringsheimConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance pringsheimConvergenceBHistCarrier :
    BHistCarrier PringsheimConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pringsheimConvergenceToEventFlow
  fromEventFlow := pringsheimConvergenceFromEventFlow

instance pringsheimConvergenceChapterTasteGate :
    ChapterTasteGate PringsheimConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      pringsheimConvergenceFromEventFlow (pringsheimConvergenceToEventFlow x) =
        some x
    exact PringsheimConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PringsheimConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PringsheimConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PringsheimConvergenceUp) ∧
      Nonempty (ChapterTasteGate PringsheimConvergenceUp) ∧
        pringsheimConvergenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨pringsheimConvergenceBHistCarrier⟩,
      ⟨pringsheimConvergenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PringsheimConvergenceUp.TasteGate
