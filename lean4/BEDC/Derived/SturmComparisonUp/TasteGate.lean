import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SturmComparisonUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SturmComparisonUp : Type where
  | mk (O0 O1 K Z W R E H C P N : BHist) : SturmComparisonUp
  deriving DecidableEq

def sturmComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sturmComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sturmComparisonEncodeBHist h

def sturmComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sturmComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sturmComparisonDecodeBHist tail)

private theorem SturmComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sturmComparisonDecodeBHist (sturmComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sturmComparisonFields : SturmComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SturmComparisonUp.mk O0 O1 K Z W R E H C P N => [O0, O1, K, Z, W, R, E, H, C, P, N]

def sturmComparisonToEventFlow : SturmComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sturmComparisonFields x).map sturmComparisonEncodeBHist

private def SturmComparisonTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SturmComparisonTasteGate_single_carrier_alignment_eventAt index rest

def sturmComparisonFromEventFlow : EventFlow → Option SturmComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SturmComparisonUp.mk
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 0 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 1 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 2 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 3 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 4 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 5 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 6 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 7 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 8 ef))
        (sturmComparisonDecodeBHist (SturmComparisonTasteGate_single_carrier_alignment_eventAt 9 ef))
        (sturmComparisonDecodeBHist
          (SturmComparisonTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem SturmComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SturmComparisonUp,
      sturmComparisonFromEventFlow (sturmComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O0 O1 K Z W R E H C P N =>
      change
        some
          (SturmComparisonUp.mk
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist O0))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist O1))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist K))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist Z))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist W))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist R))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist E))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist H))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist C))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist P))
            (sturmComparisonDecodeBHist (sturmComparisonEncodeBHist N))) =
          some (SturmComparisonUp.mk O0 O1 K Z W R E H C P N)
      rw [SturmComparisonTasteGate_single_carrier_alignment_decode O0,
        SturmComparisonTasteGate_single_carrier_alignment_decode O1,
        SturmComparisonTasteGate_single_carrier_alignment_decode K,
        SturmComparisonTasteGate_single_carrier_alignment_decode Z,
        SturmComparisonTasteGate_single_carrier_alignment_decode W,
        SturmComparisonTasteGate_single_carrier_alignment_decode R,
        SturmComparisonTasteGate_single_carrier_alignment_decode E,
        SturmComparisonTasteGate_single_carrier_alignment_decode H,
        SturmComparisonTasteGate_single_carrier_alignment_decode C,
        SturmComparisonTasteGate_single_carrier_alignment_decode P,
        SturmComparisonTasteGate_single_carrier_alignment_decode N]

private theorem SturmComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SturmComparisonUp} :
    sturmComparisonToEventFlow x = sturmComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sturmComparisonFromEventFlow (sturmComparisonToEventFlow x) =
        sturmComparisonFromEventFlow (sturmComparisonToEventFlow y) :=
    congrArg sturmComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SturmComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SturmComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance sturmComparisonBHistCarrier : BHistCarrier SturmComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sturmComparisonToEventFlow
  fromEventFlow := sturmComparisonFromEventFlow

instance sturmComparisonChapterTasteGate : ChapterTasteGate SturmComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sturmComparisonFromEventFlow (sturmComparisonToEventFlow x) = some x
    exact SturmComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SturmComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SturmComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist, sturmComparisonDecodeBHist (sturmComparisonEncodeBHist h) = h) ∧
      (∀ x : SturmComparisonUp,
        sturmComparisonFromEventFlow (sturmComparisonToEventFlow x) = some x) ∧
        (∀ x y : SturmComparisonUp,
          sturmComparisonToEventFlow x = sturmComparisonToEventFlow y → x = y) ∧
          sturmComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SturmComparisonTasteGate_single_carrier_alignment_decode,
      SturmComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SturmComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SturmComparisonUp.TasteGate
