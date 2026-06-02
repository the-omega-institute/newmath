import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySelectionPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySelectionPrincipleUp : Type where
  | mk (D W R E Q H C P N : BHist) : CauchySelectionPrincipleUp
  deriving DecidableEq

def cauchySelectionPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySelectionPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySelectionPrincipleEncodeBHist h

def cauchySelectionPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySelectionPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySelectionPrincipleDecodeBHist tail)

private theorem CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchySelectionPrincipleDecodeBHist
        (cauchySelectionPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySelectionPrincipleFields : CauchySelectionPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySelectionPrincipleUp.mk D W R E Q H C P N => [D, W, R, E, Q, H, C, P, N]

def cauchySelectionPrincipleToEventFlow : CauchySelectionPrincipleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchySelectionPrincipleFields x).map cauchySelectionPrincipleEncodeBHist

private def cauchySelectionPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySelectionPrincipleEventAtDefault index rest

def cauchySelectionPrincipleFromEventFlow
    (ef : EventFlow) : Option CauchySelectionPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySelectionPrincipleUp.mk
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 0 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 1 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 2 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 3 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 4 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 5 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 6 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 7 ef))
      (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEventAtDefault 8 ef)))

private theorem CauchySelectionPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySelectionPrincipleUp,
      cauchySelectionPrincipleFromEventFlow
        (cauchySelectionPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R E Q H C P N =>
      change
        some
          (CauchySelectionPrincipleUp.mk
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist D))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist W))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist R))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist E))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist Q))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist H))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist C))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist P))
            (cauchySelectionPrincipleDecodeBHist (cauchySelectionPrincipleEncodeBHist N))) =
          some (CauchySelectionPrincipleUp.mk D W R E Q H C P N)
      rw [CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode D,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode W,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode R,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode E,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode Q,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode H,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode C,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode P,
        CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode N]

private theorem CauchySelectionPrincipleTasteGate_single_carrier_alignment_injective
    {x y : CauchySelectionPrincipleUp} :
    cauchySelectionPrincipleToEventFlow x =
      cauchySelectionPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySelectionPrincipleFromEventFlow (cauchySelectionPrincipleToEventFlow x) =
        cauchySelectionPrincipleFromEventFlow (cauchySelectionPrincipleToEventFlow y) :=
    congrArg cauchySelectionPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySelectionPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySelectionPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySelectionPrincipleBHistCarrier :
    BHistCarrier CauchySelectionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySelectionPrincipleToEventFlow
  fromEventFlow := cauchySelectionPrincipleFromEventFlow

instance cauchySelectionPrincipleChapterTasteGate :
    ChapterTasteGate CauchySelectionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySelectionPrincipleFromEventFlow
        (cauchySelectionPrincipleToEventFlow x) = some x
    exact CauchySelectionPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySelectionPrincipleTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchySelectionPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySelectionPrincipleChapterTasteGate

theorem CauchySelectionPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySelectionPrincipleDecodeBHist
      (cauchySelectionPrincipleEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchySelectionPrincipleUp) ∧
        Nonempty (ChapterTasteGate CauchySelectionPrincipleUp) ∧
          cauchySelectionPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨CauchySelectionPrincipleTasteGate_single_carrier_alignment_decode,
      ⟨cauchySelectionPrincipleBHistCarrier⟩,
      ⟨cauchySelectionPrincipleChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchySelectionPrincipleUp
