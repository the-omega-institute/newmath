import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoreCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoreCompactUp : Type where
  | mk (X U V W K L H C P N : BHist) : CoreCompactUp
  deriving DecidableEq

def coreCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coreCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coreCompactEncodeBHist h

def coreCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coreCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coreCompactDecodeBHist tail)

private theorem CoreCompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, coreCompactDecodeBHist (coreCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def coreCompactToEventFlow : CoreCompactUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    match x with
    | CoreCompactUp.mk X U V W K L H C P N =>
        [coreCompactEncodeBHist X,
          coreCompactEncodeBHist U,
          coreCompactEncodeBHist V,
          coreCompactEncodeBHist W,
          coreCompactEncodeBHist K,
          coreCompactEncodeBHist L,
          coreCompactEncodeBHist H,
          coreCompactEncodeBHist C,
          coreCompactEncodeBHist P,
          coreCompactEncodeBHist N]

private def coreCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      coreCompactEventAtDefault index rest

def coreCompactFromEventFlow (ef : EventFlow) : Option CoreCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoreCompactUp.mk
      (coreCompactDecodeBHist (coreCompactEventAtDefault 0 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 1 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 2 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 3 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 4 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 5 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 6 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 7 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 8 ef))
      (coreCompactDecodeBHist (coreCompactEventAtDefault 9 ef)))

private theorem CoreCompactTasteGate_single_carrier_alignment_round_trip
    (x : CoreCompactUp) :
    coreCompactFromEventFlow (coreCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X U V W K L H C P N =>
      change
        some
          (CoreCompactUp.mk
            (coreCompactDecodeBHist (coreCompactEncodeBHist X))
            (coreCompactDecodeBHist (coreCompactEncodeBHist U))
            (coreCompactDecodeBHist (coreCompactEncodeBHist V))
            (coreCompactDecodeBHist (coreCompactEncodeBHist W))
            (coreCompactDecodeBHist (coreCompactEncodeBHist K))
            (coreCompactDecodeBHist (coreCompactEncodeBHist L))
            (coreCompactDecodeBHist (coreCompactEncodeBHist H))
            (coreCompactDecodeBHist (coreCompactEncodeBHist C))
            (coreCompactDecodeBHist (coreCompactEncodeBHist P))
            (coreCompactDecodeBHist (coreCompactEncodeBHist N))) =
          some (CoreCompactUp.mk X U V W K L H C P N)
      rw [CoreCompactTasteGate_single_carrier_alignment_decode_encode X,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode U,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode V,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode W,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode K,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode L,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode H,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode C,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode P,
        CoreCompactTasteGate_single_carrier_alignment_decode_encode N]

private theorem CoreCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CoreCompactUp} :
    coreCompactToEventFlow x = coreCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coreCompactFromEventFlow (coreCompactToEventFlow x) =
        coreCompactFromEventFlow (coreCompactToEventFlow y) :=
    congrArg coreCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CoreCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CoreCompactTasteGate_single_carrier_alignment_round_trip y)))

instance coreCompactBHistCarrier : BHistCarrier CoreCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coreCompactToEventFlow
  fromEventFlow := coreCompactFromEventFlow

instance coreCompactChapterTasteGate : ChapterTasteGate CoreCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact CoreCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CoreCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CoreCompactTasteGate_single_carrier_alignment :
    And (coreCompactDecodeBHist (BMark.b1 :: []) = BHist.e1 BHist.Empty)
      (And
        (forall h : BHist, coreCompactDecodeBHist (coreCompactEncodeBHist h) = h)
        (forall x : CoreCompactUp,
          coreCompactFromEventFlow (coreCompactToEventFlow x) = some x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · rfl
  · constructor
    · exact CoreCompactTasteGate_single_carrier_alignment_decode_encode
    · exact CoreCompactTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.CoreCompactUp
