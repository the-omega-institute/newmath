import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DifferentialPrivacyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DifferentialPrivacyUp : Type where
  | mk (A M O0 O1 E L F H C P N : BHist) : DifferentialPrivacyUp
  deriving DecidableEq

def differentialPrivacyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: differentialPrivacyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: differentialPrivacyEncodeBHist h

private def differentialPrivacyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (differentialPrivacyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (differentialPrivacyDecodeBHist tail)

private theorem DifferentialPrivacyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def differentialPrivacyToEventFlow : DifferentialPrivacyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DifferentialPrivacyUp.mk A M O0 O1 E L F H C P N =>
      [differentialPrivacyEncodeBHist A,
        differentialPrivacyEncodeBHist M,
        differentialPrivacyEncodeBHist O0,
        differentialPrivacyEncodeBHist O1,
        differentialPrivacyEncodeBHist E,
        differentialPrivacyEncodeBHist L,
        differentialPrivacyEncodeBHist F,
        differentialPrivacyEncodeBHist H,
        differentialPrivacyEncodeBHist C,
        differentialPrivacyEncodeBHist P,
        differentialPrivacyEncodeBHist N]

private def differentialPrivacyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => differentialPrivacyEventAtDefault index rest

private def differentialPrivacyFromEventFlow (ef : EventFlow) : Option DifferentialPrivacyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DifferentialPrivacyUp.mk
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 0 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 1 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 2 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 3 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 4 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 5 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 6 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 7 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 8 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 9 ef))
      (differentialPrivacyDecodeBHist (differentialPrivacyEventAtDefault 10 ef)))

private theorem DifferentialPrivacyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DifferentialPrivacyUp,
      differentialPrivacyFromEventFlow (differentialPrivacyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M O0 O1 E L F H C P N =>
      change
        some
          (DifferentialPrivacyUp.mk
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist A))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist M))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist O0))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist O1))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist E))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist L))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist F))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist H))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist C))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist P))
            (differentialPrivacyDecodeBHist (differentialPrivacyEncodeBHist N))) =
          some (DifferentialPrivacyUp.mk A M O0 O1 E L F H C P N)
      rw [DifferentialPrivacyTasteGate_single_carrier_alignment_decode A,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode M,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode O0,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode O1,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode E,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode L,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode F,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode H,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode C,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode P,
        DifferentialPrivacyTasteGate_single_carrier_alignment_decode N]

private theorem DifferentialPrivacyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DifferentialPrivacyUp} :
    differentialPrivacyToEventFlow x = differentialPrivacyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      differentialPrivacyFromEventFlow (differentialPrivacyToEventFlow x) =
        differentialPrivacyFromEventFlow (differentialPrivacyToEventFlow y) :=
    congrArg differentialPrivacyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DifferentialPrivacyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DifferentialPrivacyTasteGate_single_carrier_alignment_round_trip y)))

instance differentialPrivacyBHistCarrier : BHistCarrier DifferentialPrivacyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := differentialPrivacyToEventFlow
  fromEventFlow := differentialPrivacyFromEventFlow

instance differentialPrivacyChapterTasteGate : ChapterTasteGate DifferentialPrivacyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact DifferentialPrivacyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DifferentialPrivacyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DifferentialPrivacyTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DifferentialPrivacyUp) ∧
      Nonempty (ChapterTasteGate DifferentialPrivacyUp) ∧
        differentialPrivacyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨differentialPrivacyBHistCarrier⟩
  · constructor
    · exact ⟨differentialPrivacyChapterTasteGate⟩
    · rfl

end BEDC.Derived.DifferentialPrivacyUp.TasteGate
