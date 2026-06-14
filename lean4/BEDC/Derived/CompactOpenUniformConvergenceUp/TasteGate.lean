import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOpenUniformConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactOpenUniformConvergenceUp : Type where
  | mk (F K E Q M G D R H C P N : BHist) : CompactOpenUniformConvergenceUp
  deriving DecidableEq

def compactOpenUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOpenUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOpenUniformConvergenceEncodeBHist h

def compactOpenUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOpenUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOpenUniformConvergenceDecodeBHist tail)

private theorem compactOpenUniformConvergenceDecodeEncode :
    ∀ h : BHist,
      compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def compactOpenUniformConvergenceFields :
    CompactOpenUniformConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOpenUniformConvergenceUp.mk F K E Q M G D R H C P N =>
      [F, K, E, Q, M, G, D, R, H, C, P, N]

def compactOpenUniformConvergenceToEventFlow :
    CompactOpenUniformConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactOpenUniformConvergenceFields x).map
      compactOpenUniformConvergenceEncodeBHist

private def compactOpenUniformConvergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactOpenUniformConvergenceEventAtDefault index rest

def compactOpenUniformConvergenceFromEventFlow
    (ef : EventFlow) : Option CompactOpenUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactOpenUniformConvergenceUp.mk
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 0 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 1 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 2 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 3 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 4 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 5 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 6 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 7 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 8 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 9 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 10 ef))
      (compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEventAtDefault 11 ef)))

private theorem compactOpenUniformConvergenceRoundTrip :
    ∀ x : CompactOpenUniformConvergenceUp,
      compactOpenUniformConvergenceFromEventFlow
        (compactOpenUniformConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F K E Q M G D R H C P N =>
      change
        some
          (CompactOpenUniformConvergenceUp.mk
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist F))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist K))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist E))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist Q))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist M))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist G))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist D))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist R))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist H))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist C))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist P))
            (compactOpenUniformConvergenceDecodeBHist
              (compactOpenUniformConvergenceEncodeBHist N))) =
          some (CompactOpenUniformConvergenceUp.mk F K E Q M G D R H C P N)
      rw [compactOpenUniformConvergenceDecodeEncode F,
        compactOpenUniformConvergenceDecodeEncode K,
        compactOpenUniformConvergenceDecodeEncode E,
        compactOpenUniformConvergenceDecodeEncode Q,
        compactOpenUniformConvergenceDecodeEncode M,
        compactOpenUniformConvergenceDecodeEncode G,
        compactOpenUniformConvergenceDecodeEncode D,
        compactOpenUniformConvergenceDecodeEncode R,
        compactOpenUniformConvergenceDecodeEncode H,
        compactOpenUniformConvergenceDecodeEncode C,
        compactOpenUniformConvergenceDecodeEncode P,
        compactOpenUniformConvergenceDecodeEncode N]

private theorem compactOpenUniformConvergenceToEventFlow_injective
    {x y : CompactOpenUniformConvergenceUp} :
    compactOpenUniformConvergenceToEventFlow x =
      compactOpenUniformConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOpenUniformConvergenceFromEventFlow
          (compactOpenUniformConvergenceToEventFlow x) =
        compactOpenUniformConvergenceFromEventFlow
          (compactOpenUniformConvergenceToEventFlow y) :=
    congrArg compactOpenUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactOpenUniformConvergenceRoundTrip x).symm
      (Eq.trans hread (compactOpenUniformConvergenceRoundTrip y)))

instance compactOpenUniformConvergenceBHistCarrier :
    BHistCarrier CompactOpenUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOpenUniformConvergenceToEventFlow
  fromEventFlow := compactOpenUniformConvergenceFromEventFlow

instance compactOpenUniformConvergenceChapterTasteGate :
    ChapterTasteGate CompactOpenUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactOpenUniformConvergenceFromEventFlow
        (compactOpenUniformConvergenceToEventFlow x) = some x
    exact compactOpenUniformConvergenceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactOpenUniformConvergenceToEventFlow_injective heq)

theorem CompactOpenUniformConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactOpenUniformConvergenceDecodeBHist
        (compactOpenUniformConvergenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactOpenUniformConvergenceUp) ∧
        Nonempty (ChapterTasteGate CompactOpenUniformConvergenceUp) ∧
          compactOpenUniformConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactOpenUniformConvergenceDecodeEncode,
      ⟨compactOpenUniformConvergenceBHistCarrier⟩,
      ⟨compactOpenUniformConvergenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CompactOpenUniformConvergenceUp
