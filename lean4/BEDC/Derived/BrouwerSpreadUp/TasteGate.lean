import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerSpreadUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerSpreadUp : Type where
  | mk (T S W A H C P N : BHist) : BrouwerSpreadUp
  deriving DecidableEq

def brouwerSpreadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerSpreadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerSpreadEncodeBHist h

def brouwerSpreadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerSpreadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerSpreadDecodeBHist tail)

private theorem BrouwerSpreadTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerSpreadFields : BrouwerSpreadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerSpreadUp.mk T S W A H C P N => [T, S, W, A, H, C, P, N]

def brouwerSpreadToEventFlow : BrouwerSpreadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (brouwerSpreadFields x).map brouwerSpreadEncodeBHist

private def brouwerSpreadEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerSpreadEventAtDefault index rest

def brouwerSpreadFromEventFlow (ef : EventFlow) : Option BrouwerSpreadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerSpreadUp.mk
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 0 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 1 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 2 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 3 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 4 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 5 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 6 ef))
      (brouwerSpreadDecodeBHist (brouwerSpreadEventAtDefault 7 ef)))

private theorem BrouwerSpreadTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BrouwerSpreadUp,
      brouwerSpreadFromEventFlow (brouwerSpreadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S W A H C P N =>
      change
        some
          (BrouwerSpreadUp.mk
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist T))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist S))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist W))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist A))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist H))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist C))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist P))
            (brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist N))) =
          some (BrouwerSpreadUp.mk T S W A H C P N)
      rw [BrouwerSpreadTasteGate_single_carrier_alignment_decode T,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode S,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode W,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode A,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode H,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode C,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode P,
        BrouwerSpreadTasteGate_single_carrier_alignment_decode N]

private theorem BrouwerSpreadTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BrouwerSpreadUp} :
    brouwerSpreadToEventFlow x = brouwerSpreadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerSpreadFromEventFlow (brouwerSpreadToEventFlow x) =
        brouwerSpreadFromEventFlow (brouwerSpreadToEventFlow y) :=
    congrArg brouwerSpreadFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BrouwerSpreadTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BrouwerSpreadTasteGate_single_carrier_alignment_round_trip y)))

instance brouwerSpreadBHistCarrier : BHistCarrier BrouwerSpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerSpreadToEventFlow
  fromEventFlow := brouwerSpreadFromEventFlow

instance brouwerSpreadChapterTasteGate : ChapterTasteGate BrouwerSpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerSpreadFromEventFlow (brouwerSpreadToEventFlow x) = some x
    exact BrouwerSpreadTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrouwerSpreadTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BrouwerSpreadTasteGate_single_carrier_alignment :
    (∀ h : BHist, brouwerSpreadDecodeBHist (brouwerSpreadEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BrouwerSpreadUp) ∧
        Nonempty (ChapterTasteGate BrouwerSpreadUp) ∧
          brouwerSpreadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BrouwerSpreadTasteGate_single_carrier_alignment_decode,
      ⟨brouwerSpreadBHistCarrier⟩,
      ⟨brouwerSpreadChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BrouwerSpreadUp
