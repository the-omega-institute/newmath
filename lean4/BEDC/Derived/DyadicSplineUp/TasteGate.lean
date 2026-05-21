import BEDC.Derived.DyadicSplineUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSplineUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSplineUp : Type where
  | mk (knots coeffs segments cells readback sealRow transport route provenance nameCert : BHist) :
      DyadicSplineUp
  deriving DecidableEq

def dyadicSplineEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicSplineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicSplineEncodeBHist h

def dyadicSplineDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicSplineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicSplineDecodeBHist tail)

private theorem DyadicSplineTasteGate_single_carrier_alignment_decode :
    forall h : BHist, dyadicSplineDecodeBHist (dyadicSplineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicSplineFields : DyadicSplineUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSplineUp.mk knots coeffs segments cells readback sealRow transport route provenance
      nameCert =>
      [knots, coeffs, segments, cells, readback, sealRow, transport, route, provenance, nameCert]

def dyadicSplineToEventFlow : DyadicSplineUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicSplineFields x).map dyadicSplineEncodeBHist

private def dyadicSplineEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicSplineEventAtDefault index rest

def dyadicSplineFromEventFlow (ef : EventFlow) : Option DyadicSplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicSplineUp.mk
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 0 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 1 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 2 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 3 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 4 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 5 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 6 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 7 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 8 ef))
      (dyadicSplineDecodeBHist (dyadicSplineEventAtDefault 9 ef)))

private theorem DyadicSplineTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicSplineUp,
      dyadicSplineFromEventFlow (dyadicSplineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro packet
  cases packet with
  | mk knots coeffs segments cells readback sealRow transport route provenance nameCert =>
      change
        some
          (DyadicSplineUp.mk
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist knots))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist coeffs))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist segments))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist cells))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist readback))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist sealRow))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist transport))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist route))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist provenance))
            (dyadicSplineDecodeBHist (dyadicSplineEncodeBHist nameCert))) =
          some
            (DyadicSplineUp.mk knots coeffs segments cells readback sealRow transport route
              provenance nameCert)
      rw [DyadicSplineTasteGate_single_carrier_alignment_decode knots,
        DyadicSplineTasteGate_single_carrier_alignment_decode coeffs,
        DyadicSplineTasteGate_single_carrier_alignment_decode segments,
        DyadicSplineTasteGate_single_carrier_alignment_decode cells,
        DyadicSplineTasteGate_single_carrier_alignment_decode readback,
        DyadicSplineTasteGate_single_carrier_alignment_decode sealRow,
        DyadicSplineTasteGate_single_carrier_alignment_decode transport,
        DyadicSplineTasteGate_single_carrier_alignment_decode route,
        DyadicSplineTasteGate_single_carrier_alignment_decode provenance,
        DyadicSplineTasteGate_single_carrier_alignment_decode nameCert]

private theorem dyadicSplineToEventFlow_injective {x y : DyadicSplineUp} :
    dyadicSplineToEventFlow x = dyadicSplineToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicSplineFromEventFlow (dyadicSplineToEventFlow x) =
        dyadicSplineFromEventFlow (dyadicSplineToEventFlow y) :=
    congrArg dyadicSplineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicSplineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicSplineTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicSplineTasteGate_single_carrier_alignment_fields :
    forall x y : DyadicSplineUp, dyadicSplineFields x = dyadicSplineFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk knots1 coeffs1 segments1 cells1 readback1 seal1 transport1 route1 provenance1 nameCert1 =>
      cases y with
      | mk knots2 coeffs2 segments2 cells2 readback2 seal2 transport2 route2 provenance2 nameCert2 =>
          cases hfields
          rfl

instance dyadicSplineBHistCarrier : BHistCarrier DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicSplineToEventFlow
  fromEventFlow := dyadicSplineFromEventFlow

instance dyadicSplineChapterTasteGate : ChapterTasteGate DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicSplineFromEventFlow (dyadicSplineToEventFlow x) = some x
    exact DyadicSplineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicSplineToEventFlow_injective heq)

instance dyadicSplineFieldFaithful : FieldFaithful DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicSplineFields
  field_faithful := DyadicSplineTasteGate_single_carrier_alignment_fields

instance dyadicSplineNontrivial : Nontrivial DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSplineUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicSplineUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSplineChapterTasteGate

theorem DyadicSplineTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicSplineUp) ∧
      Nonempty (FieldFaithful DyadicSplineUp) ∧
        Nonempty (Nontrivial DyadicSplineUp) ∧
          (forall h : BHist, dyadicSplineDecodeBHist (dyadicSplineEncodeBHist h) = h) ∧
            (forall x : DyadicSplineUp,
              dyadicSplineFromEventFlow (dyadicSplineToEventFlow x) = some x) ∧
              (forall x y : DyadicSplineUp,
                dyadicSplineToEventFlow x = dyadicSplineToEventFlow y -> x = y) ∧
                dyadicSplineFields
                    (DyadicSplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
                  [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                    BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
                  dyadicSplineToEventFlow
                      (DyadicSplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
                    [[], [], [], [], [], [], [], [], [], []] ∧
                    dyadicSplineEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨dyadicSplineChapterTasteGate⟩,
      ⟨dyadicSplineFieldFaithful⟩,
      ⟨dyadicSplineNontrivial⟩,
      DyadicSplineTasteGate_single_carrier_alignment_decode,
      DyadicSplineTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => dyadicSplineToEventFlow_injective heq),
      rfl,
      rfl,
      rfl⟩

end BEDC.Derived.DyadicSplineUp.TasteGate
