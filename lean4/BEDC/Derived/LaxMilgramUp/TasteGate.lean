import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LaxMilgramUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LaxMilgramUp : Type where
  | mk (H B F C S T P N : BHist) : LaxMilgramUp
  deriving DecidableEq

def laxMilgramEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: laxMilgramEncodeBHist h
  | BHist.e1 h => BMark.b1 :: laxMilgramEncodeBHist h

def laxMilgramDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (laxMilgramDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (laxMilgramDecodeBHist tail)

private theorem LaxMilgramTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, laxMilgramDecodeBHist (laxMilgramEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def laxMilgramFields : LaxMilgramUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LaxMilgramUp.mk H B F C S T P N => [H, B, F, C, S, T, P, N]

def laxMilgramToEventFlow : LaxMilgramUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (laxMilgramFields x).map laxMilgramEncodeBHist

private def laxMilgramEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => laxMilgramEventAtDefault index rest

def laxMilgramFromEventFlow (ef : EventFlow) : Option LaxMilgramUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LaxMilgramUp.mk
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 0 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 1 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 2 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 3 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 4 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 5 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 6 ef))
      (laxMilgramDecodeBHist (laxMilgramEventAtDefault 7 ef)))

private theorem LaxMilgramTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LaxMilgramUp,
      laxMilgramFromEventFlow (laxMilgramToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H B F C S T P N =>
      change
        some
          (LaxMilgramUp.mk
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist H))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist B))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist F))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist C))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist S))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist T))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist P))
            (laxMilgramDecodeBHist (laxMilgramEncodeBHist N))) =
          some (LaxMilgramUp.mk H B F C S T P N)
      rw [LaxMilgramTasteGate_single_carrier_alignment_decode H,
        LaxMilgramTasteGate_single_carrier_alignment_decode B,
        LaxMilgramTasteGate_single_carrier_alignment_decode F,
        LaxMilgramTasteGate_single_carrier_alignment_decode C,
        LaxMilgramTasteGate_single_carrier_alignment_decode S,
        LaxMilgramTasteGate_single_carrier_alignment_decode T,
        LaxMilgramTasteGate_single_carrier_alignment_decode P,
        LaxMilgramTasteGate_single_carrier_alignment_decode N]

private theorem LaxMilgramTasteGate_single_carrier_alignment_injective
    {x y : LaxMilgramUp} :
    laxMilgramToEventFlow x = laxMilgramToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      laxMilgramFromEventFlow (laxMilgramToEventFlow x) =
        laxMilgramFromEventFlow (laxMilgramToEventFlow y) :=
    congrArg laxMilgramFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LaxMilgramTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LaxMilgramTasteGate_single_carrier_alignment_round_trip y)))

instance laxMilgramBHistCarrier : BHistCarrier LaxMilgramUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := laxMilgramToEventFlow
  fromEventFlow := laxMilgramFromEventFlow

instance laxMilgramChapterTasteGate : ChapterTasteGate LaxMilgramUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change laxMilgramFromEventFlow (laxMilgramToEventFlow x) = some x
    exact LaxMilgramTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LaxMilgramTasteGate_single_carrier_alignment_injective heq)

instance laxMilgramNontrivial : Nontrivial LaxMilgramUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LaxMilgramUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LaxMilgramUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LaxMilgramUp :=
  -- BEDC touchpoint anchor: BHist BMark
  laxMilgramChapterTasteGate

theorem LaxMilgramTasteGate_single_carrier_alignment :
    (∀ h : BHist, laxMilgramDecodeBHist (laxMilgramEncodeBHist h) = h) ∧
      (∀ x : LaxMilgramUp,
        laxMilgramFromEventFlow (laxMilgramToEventFlow x) = some x) ∧
        (∀ x y : LaxMilgramUp,
          laxMilgramToEventFlow x = laxMilgramToEventFlow y → x = y) ∧
          laxMilgramEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Nontrivial
  exact
    ⟨LaxMilgramTasteGate_single_carrier_alignment_decode,
      LaxMilgramTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LaxMilgramTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.LaxMilgramUp
