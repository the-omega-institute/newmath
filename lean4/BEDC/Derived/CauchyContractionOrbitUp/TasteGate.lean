import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContractionOrbitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContractionOrbitUp : Type where
  | mk (X T I L M R E H C P N : BHist) : CauchyContractionOrbitUp
  deriving DecidableEq

def cauchyContractionOrbitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContractionOrbitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContractionOrbitEncodeBHist h

def cauchyContractionOrbitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContractionOrbitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContractionOrbitDecodeBHist tail)

private theorem CauchyContractionOrbitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContractionOrbitToEventFlow : CauchyContractionOrbitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContractionOrbitUp.mk X T I L M R E H C P N =>
      [cauchyContractionOrbitEncodeBHist X,
        cauchyContractionOrbitEncodeBHist T,
        cauchyContractionOrbitEncodeBHist I,
        cauchyContractionOrbitEncodeBHist L,
        cauchyContractionOrbitEncodeBHist M,
        cauchyContractionOrbitEncodeBHist R,
        cauchyContractionOrbitEncodeBHist E,
        cauchyContractionOrbitEncodeBHist H,
        cauchyContractionOrbitEncodeBHist C,
        cauchyContractionOrbitEncodeBHist P,
        cauchyContractionOrbitEncodeBHist N]

private def cauchyContractionOrbitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContractionOrbitEventAtDefault index rest

def cauchyContractionOrbitFromEventFlow
    (ef : EventFlow) : Option CauchyContractionOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContractionOrbitUp.mk
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 0 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 1 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 2 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 3 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 4 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 5 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 6 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 7 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 8 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 9 ef))
      (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEventAtDefault 10 ef)))

private theorem CauchyContractionOrbitTasteGate_single_carrier_alignment_round_trip
    (x : CauchyContractionOrbitUp) :
    cauchyContractionOrbitFromEventFlow
      (cauchyContractionOrbitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T I L M R E H C P N =>
      change
        some
          (CauchyContractionOrbitUp.mk
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist X))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist T))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist I))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist L))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist M))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist R))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist E))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist H))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist C))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist P))
            (cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist N))) =
          some (CauchyContractionOrbitUp.mk X T I L M R E H C P N)
      rw [CauchyContractionOrbitTasteGate_single_carrier_alignment_decode X,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode T,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode I,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode L,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode M,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode R,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode E,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode H,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode C,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode P,
        CauchyContractionOrbitTasteGate_single_carrier_alignment_decode N]

private theorem cauchyContractionOrbitToEventFlow_injective
    {x y : CauchyContractionOrbitUp} :
    cauchyContractionOrbitToEventFlow x = cauchyContractionOrbitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContractionOrbitFromEventFlow (cauchyContractionOrbitToEventFlow x) =
        cauchyContractionOrbitFromEventFlow (cauchyContractionOrbitToEventFlow y) :=
    congrArg cauchyContractionOrbitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyContractionOrbitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyContractionOrbitTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyContractionOrbitBHistCarrier : BHistCarrier CauchyContractionOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContractionOrbitToEventFlow
  fromEventFlow := cauchyContractionOrbitFromEventFlow

instance cauchyContractionOrbitChapterTasteGate :
    ChapterTasteGate CauchyContractionOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyContractionOrbitFromEventFlow
        (cauchyContractionOrbitToEventFlow x) = some x
    exact CauchyContractionOrbitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContractionOrbitToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyContractionOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContractionOrbitChapterTasteGate

theorem CauchyContractionOrbitTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyContractionOrbitUp) ∧
      Nonempty (ChapterTasteGate CauchyContractionOrbitUp) ∧
      (∀ h : BHist,
        cauchyContractionOrbitDecodeBHist (cauchyContractionOrbitEncodeBHist h) = h) ∧
      (∀ x : CauchyContractionOrbitUp,
        cauchyContractionOrbitFromEventFlow (cauchyContractionOrbitToEventFlow x) =
          some x) ∧
      cauchyContractionOrbitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyContractionOrbitBHistCarrier⟩
  constructor
  · exact ⟨cauchyContractionOrbitChapterTasteGate⟩
  constructor
  · exact CauchyContractionOrbitTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyContractionOrbitTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.CauchyContractionOrbitUp
