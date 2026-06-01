import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticEquivalenceUp : Type where
  | mk (S0 S1 R0 R1 D T E H C P N : BHist) : AsymptoticEquivalenceUp
  deriving DecidableEq

def asymptoticEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticEquivalenceEncodeBHist h

def asymptoticEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticEquivalenceDecodeBHist tail)

private theorem asymptoticEquivalenceDecodeEncode :
    ∀ h : BHist,
      asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def asymptoticEquivalenceFields : AsymptoticEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N =>
      [S0, S1, R0, R1, D, T, E, H, C, P, N]

def asymptoticEquivalenceToEventFlow : AsymptoticEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (asymptoticEquivalenceFields x).map asymptoticEquivalenceEncodeBHist

private def asymptoticEquivalenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => asymptoticEquivalenceEventAt index rest

def asymptoticEquivalenceFromEventFlow (ef : EventFlow) : Option AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticEquivalenceUp.mk
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 0 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 1 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 2 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 3 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 4 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 5 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 6 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 7 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 8 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 9 ef))
      (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEventAt 10 ef)))

private theorem asymptoticEquivalenceRoundTrip (x : AsymptoticEquivalenceUp) :
    asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S0 S1 R0 R1 D T E H C P N =>
      change
        some
          (AsymptoticEquivalenceUp.mk
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S0))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S1))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R0))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R1))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist D))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist T))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist E))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist H))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist C))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist P))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist N))) =
          some (AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N)
      rw [asymptoticEquivalenceDecodeEncode S0,
        asymptoticEquivalenceDecodeEncode S1,
        asymptoticEquivalenceDecodeEncode R0,
        asymptoticEquivalenceDecodeEncode R1,
        asymptoticEquivalenceDecodeEncode D,
        asymptoticEquivalenceDecodeEncode T,
        asymptoticEquivalenceDecodeEncode E,
        asymptoticEquivalenceDecodeEncode H,
        asymptoticEquivalenceDecodeEncode C,
        asymptoticEquivalenceDecodeEncode P,
        asymptoticEquivalenceDecodeEncode N]

private theorem asymptoticEquivalenceToEventFlow_injective {x y : AsymptoticEquivalenceUp} :
    asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow y) :=
    congrArg asymptoticEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (asymptoticEquivalenceRoundTrip x).symm
      (Eq.trans hread (asymptoticEquivalenceRoundTrip y)))

instance asymptoticEquivalenceBHistCarrier : BHistCarrier AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticEquivalenceToEventFlow
  fromEventFlow := asymptoticEquivalenceFromEventFlow

instance asymptoticEquivalenceChapterTasteGate :
    ChapterTasteGate AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) = some x
    exact asymptoticEquivalenceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (asymptoticEquivalenceToEventFlow_injective heq)

theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AsymptoticEquivalenceUp) ∧
        Nonempty (ChapterTasteGate AsymptoticEquivalenceUp) ∧
          asymptoticEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨asymptoticEquivalenceDecodeEncode,
      ⟨⟨asymptoticEquivalenceBHistCarrier⟩, ⟨asymptoticEquivalenceChapterTasteGate⟩, rfl⟩⟩

end BEDC.Derived.AsymptoticEquivalenceUp
