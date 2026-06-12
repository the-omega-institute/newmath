import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CoveringDimensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CoveringDimensionUp : Type where
  | mk (K E C R O L H T P N : BHist) : CoveringDimensionUp
  deriving DecidableEq

def coveringDimensionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: coveringDimensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: coveringDimensionEncodeBHist h

def coveringDimensionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (coveringDimensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (coveringDimensionDecodeBHist tail)

private theorem CoveringDimensionTasteGate_single_carrier_alignment_decode :
    forall h : BHist, coveringDimensionDecodeBHist (coveringDimensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def coveringDimensionFields : CoveringDimensionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoveringDimensionUp.mk K E C R O L H T P N => [K, E, C, R, O, L, H, T, P, N]

def coveringDimensionToEventFlow : CoveringDimensionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (coveringDimensionFields x).map coveringDimensionEncodeBHist

private def coveringDimensionRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => coveringDimensionRawAt index rest

def coveringDimensionFromEventFlow (flow : EventFlow) : Option CoveringDimensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoveringDimensionUp.mk
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 0 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 1 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 2 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 3 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 4 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 5 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 6 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 7 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 8 flow))
      (coveringDimensionDecodeBHist (coveringDimensionRawAt 9 flow)))

private theorem CoveringDimensionTasteGate_single_carrier_alignment_round_trip :
    forall x : CoveringDimensionUp,
      coveringDimensionFromEventFlow (coveringDimensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K E C R O L H T P N =>
      change
        some
          (CoveringDimensionUp.mk
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist K))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist E))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist C))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist R))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist O))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist L))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist H))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist T))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist P))
            (coveringDimensionDecodeBHist (coveringDimensionEncodeBHist N))) =
          some (CoveringDimensionUp.mk K E C R O L H T P N)
      rw [CoveringDimensionTasteGate_single_carrier_alignment_decode K,
        CoveringDimensionTasteGate_single_carrier_alignment_decode E,
        CoveringDimensionTasteGate_single_carrier_alignment_decode C,
        CoveringDimensionTasteGate_single_carrier_alignment_decode R,
        CoveringDimensionTasteGate_single_carrier_alignment_decode O,
        CoveringDimensionTasteGate_single_carrier_alignment_decode L,
        CoveringDimensionTasteGate_single_carrier_alignment_decode H,
        CoveringDimensionTasteGate_single_carrier_alignment_decode T,
        CoveringDimensionTasteGate_single_carrier_alignment_decode P,
        CoveringDimensionTasteGate_single_carrier_alignment_decode N]

private theorem coveringDimensionToEventFlow_injective {x y : CoveringDimensionUp} :
    coveringDimensionToEventFlow x = coveringDimensionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      coveringDimensionFromEventFlow (coveringDimensionToEventFlow x) =
        coveringDimensionFromEventFlow (coveringDimensionToEventFlow y) :=
    congrArg coveringDimensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CoveringDimensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CoveringDimensionTasteGate_single_carrier_alignment_round_trip y)))

instance coveringDimensionBHistCarrier : BHistCarrier CoveringDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := coveringDimensionToEventFlow
  fromEventFlow := coveringDimensionFromEventFlow

instance coveringDimensionChapterTasteGate : ChapterTasteGate CoveringDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change coveringDimensionFromEventFlow (coveringDimensionToEventFlow x) = some x
    exact CoveringDimensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (coveringDimensionToEventFlow_injective heq)

instance coveringDimensionFieldFaithful : FieldFaithful CoveringDimensionUp where
  fields := coveringDimensionFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk K1 E1 C1 R1 O1 L1 H1 T1 P1 N1 =>
      cases y with
      | mk K2 E2 C2 R2 O2 L2 H2 T2 P2 N2 =>
        simp only [coveringDimensionFields] at h
        injection h with hK tail1
        injection tail1 with hE tail2
        injection tail2 with hC tail3
        injection tail3 with hR tail4
        injection tail4 with hO tail5
        injection tail5 with hL tail6
        injection tail6 with hH tail7
        injection tail7 with hT tail8
        injection tail8 with hP tail9
        injection tail9 with hN _
        subst hK; subst hE; subst hC; subst hR; subst hO
        subst hL; subst hH; subst hT; subst hP; subst hN
        rfl

def taste_gate : ChapterTasteGate CoveringDimensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  coveringDimensionChapterTasteGate

theorem CoveringDimensionTasteGate_single_carrier_alignment :
    (forall h : BHist, coveringDimensionDecodeBHist (coveringDimensionEncodeBHist h) = h) ∧
      (forall x : CoveringDimensionUp,
        coveringDimensionFromEventFlow (coveringDimensionToEventFlow x) = some x) ∧
      (forall x y : CoveringDimensionUp,
        coveringDimensionToEventFlow x = coveringDimensionToEventFlow y -> x = y) ∧
      coveringDimensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CoveringDimensionTasteGate_single_carrier_alignment_decode,
      CoveringDimensionTasteGate_single_carrier_alignment_round_trip,
      (fun _x _y heq => coveringDimensionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CoveringDimensionUp
