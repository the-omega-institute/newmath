import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBisectionTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBisectionTreeUp : Type where
  | mk (D I T W R E H C P N : BHist) : DyadicBisectionTreeUp
  deriving DecidableEq

def dyadicBisectionTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBisectionTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBisectionTreeEncodeBHist h

def dyadicBisectionTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBisectionTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBisectionTreeDecodeBHist tail)

private theorem DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicBisectionTreeFields : DyadicBisectionTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBisectionTreeUp.mk D I T W R E H C P N =>
      [D, I, T, W, R, E, H, C, P, N]

def dyadicBisectionTreeToEventFlow : DyadicBisectionTreeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicBisectionTreeFields x).map dyadicBisectionTreeEncodeBHist

private def dyadicBisectionTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicBisectionTreeEventAtDefault index rest

def dyadicBisectionTreeFromEventFlow (ef : EventFlow) : Option DyadicBisectionTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicBisectionTreeUp.mk
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 0 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 1 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 2 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 3 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 4 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 5 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 6 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 7 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 8 ef))
      (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEventAtDefault 9 ef)))

private theorem DyadicBisectionTreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicBisectionTreeUp,
      dyadicBisectionTreeFromEventFlow (dyadicBisectionTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D I T W R E H C P N =>
      change
        some
          (DyadicBisectionTreeUp.mk
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist D))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist I))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist T))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist W))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist R))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist E))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist H))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist C))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist P))
            (dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist N))) =
          some (DyadicBisectionTreeUp.mk D I T W R E H C P N)
      rw [DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode D,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode I,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode T,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode W,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode R,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode E,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode H,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode C,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode P,
        DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicBisectionTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicBisectionTreeUp} :
    dyadicBisectionTreeToEventFlow x = dyadicBisectionTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBisectionTreeFromEventFlow (dyadicBisectionTreeToEventFlow x) =
        dyadicBisectionTreeFromEventFlow (dyadicBisectionTreeToEventFlow y) :=
    congrArg dyadicBisectionTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicBisectionTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicBisectionTreeTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicBisectionTreeBHistCarrier : BHistCarrier DyadicBisectionTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBisectionTreeToEventFlow
  fromEventFlow := dyadicBisectionTreeFromEventFlow

instance dyadicBisectionTreeChapterTasteGate :
    ChapterTasteGate DyadicBisectionTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicBisectionTreeFromEventFlow (dyadicBisectionTreeToEventFlow x) = some x
    exact DyadicBisectionTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicBisectionTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicBisectionTreeTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier DyadicBisectionTreeUp,
      Nonempty (@ChapterTasteGate DyadicBisectionTreeUp carrier)) ∧
      (∀ h : BHist, dyadicBisectionTreeDecodeBHist (dyadicBisectionTreeEncodeBHist h) = h) ∧
        (∀ x : DyadicBisectionTreeUp,
          dyadicBisectionTreeFromEventFlow (dyadicBisectionTreeToEventFlow x) = some x) ∧
          dyadicBisectionTreeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨dyadicBisectionTreeBHistCarrier, Nonempty.intro dyadicBisectionTreeChapterTasteGate⟩,
      DyadicBisectionTreeTasteGate_single_carrier_alignment_decode_encode,
      DyadicBisectionTreeTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.DyadicBisectionTreeUp
