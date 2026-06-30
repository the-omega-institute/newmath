import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionFilterSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionFilterSeparationUp : Type where
  | mk
      (filterRow hausdorffRow separatedRow completionRow metricRow realRow localName : BHist) :
      HausdorffCompletionFilterSeparationUp

def hausdorffCompletionFilterSeparationFields :
    HausdorffCompletionFilterSeparationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionFilterSeparationUp.mk filterRow hausdorffRow separatedRow completionRow
      metricRow realRow localName =>
      [filterRow, hausdorffRow, separatedRow, completionRow, metricRow, realRow, localName]

def hausdorffCompletionFilterSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionFilterSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionFilterSeparationEncodeBHist h

def hausdorffCompletionFilterSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionFilterSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionFilterSeparationDecodeBHist tail)

private theorem hausdorffCompletionFilterSeparation_decode_encode_bhist :
    ∀ h : BHist,
      hausdorffCompletionFilterSeparationDecodeBHist
        (hausdorffCompletionFilterSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem hausdorffCompletionFilterSeparationEncodeBHist_injective {h k : BHist} :
    hausdorffCompletionFilterSeparationEncodeBHist h =
        hausdorffCompletionFilterSeparationEncodeBHist k →
      h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEncodeBHist h) =
        hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEncodeBHist k) :=
    congrArg hausdorffCompletionFilterSeparationDecodeBHist heq
  exact
    Eq.trans (hausdorffCompletionFilterSeparation_decode_encode_bhist h).symm
      (Eq.trans hdecode (hausdorffCompletionFilterSeparation_decode_encode_bhist k))

private theorem hausdorffCompletionFilterSeparation_mk_congr
    {filterRow filterRow' hausdorffRow hausdorffRow' separatedRow separatedRow'
      completionRow completionRow' metricRow metricRow' realRow realRow'
      localName localName' : BHist}
    (hFilter : filterRow' = filterRow)
    (hHausdorff : hausdorffRow' = hausdorffRow)
    (hSeparated : separatedRow' = separatedRow)
    (hCompletion : completionRow' = completionRow)
    (hMetric : metricRow' = metricRow)
    (hReal : realRow' = realRow)
    (hLocalName : localName' = localName) :
    HausdorffCompletionFilterSeparationUp.mk filterRow' hausdorffRow' separatedRow'
        completionRow' metricRow' realRow' localName' =
      HausdorffCompletionFilterSeparationUp.mk filterRow hausdorffRow separatedRow
        completionRow metricRow realRow localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFilter
  cases hHausdorff
  cases hSeparated
  cases hCompletion
  cases hMetric
  cases hReal
  cases hLocalName
  rfl

def hausdorffCompletionFilterSeparationToEventFlow :
    HausdorffCompletionFilterSeparationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (hausdorffCompletionFilterSeparationFields x).map
      hausdorffCompletionFilterSeparationEncodeBHist

private def hausdorffCompletionFilterSeparationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hausdorffCompletionFilterSeparationEventAtDefault index rest

def hausdorffCompletionFilterSeparationFromEventFlow :
    EventFlow → Option HausdorffCompletionFilterSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (HausdorffCompletionFilterSeparationUp.mk
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 0 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 1 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 2 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 3 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 4 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 5 flow))
        (hausdorffCompletionFilterSeparationDecodeBHist
          (hausdorffCompletionFilterSeparationEventAtDefault 6 flow)))

private theorem hausdorffCompletionFilterSeparation_round_trip :
    ∀ x : HausdorffCompletionFilterSeparationUp,
      hausdorffCompletionFilterSeparationFromEventFlow
        (hausdorffCompletionFilterSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filterRow hausdorffRow separatedRow completionRow metricRow realRow localName =>
      change
        some
          (HausdorffCompletionFilterSeparationUp.mk
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist filterRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist hausdorffRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist separatedRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist completionRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist metricRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist realRow))
            (hausdorffCompletionFilterSeparationDecodeBHist
              (hausdorffCompletionFilterSeparationEncodeBHist localName))) =
          some
            (HausdorffCompletionFilterSeparationUp.mk filterRow hausdorffRow separatedRow
              completionRow metricRow realRow localName)
      exact
        congrArg some
          (hausdorffCompletionFilterSeparation_mk_congr
            (hausdorffCompletionFilterSeparation_decode_encode_bhist filterRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist hausdorffRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist separatedRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist completionRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist metricRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist realRow)
            (hausdorffCompletionFilterSeparation_decode_encode_bhist localName))

private theorem hausdorffCompletionFilterSeparationToEventFlow_injective
    {x y : HausdorffCompletionFilterSeparationUp} :
    hausdorffCompletionFilterSeparationToEventFlow x =
        hausdorffCompletionFilterSeparationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk filterRow hausdorffRow separatedRow completionRow metricRow realRow localName =>
      cases y with
      | mk filterRow' hausdorffRow' separatedRow' completionRow' metricRow' realRow'
          localName' =>
          injection heq with filterEq tailEq0
          injection tailEq0 with hausdorffEq tailEq1
          injection tailEq1 with separatedEq tailEq2
          injection tailEq2 with completionEq tailEq3
          injection tailEq3 with metricEq tailEq4
          injection tailEq4 with realEq tailEq5
          injection tailEq5 with localNameEq _nilEq
          exact
            hausdorffCompletionFilterSeparation_mk_congr
              (hausdorffCompletionFilterSeparationEncodeBHist_injective filterEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective hausdorffEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective separatedEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective completionEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective metricEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective realEq)
              (hausdorffCompletionFilterSeparationEncodeBHist_injective localNameEq)

instance hausdorffCompletionFilterSeparationBHistCarrier :
    BHistCarrier HausdorffCompletionFilterSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionFilterSeparationToEventFlow
  fromEventFlow := hausdorffCompletionFilterSeparationFromEventFlow

instance hausdorffCompletionFilterSeparationChapterTasteGate :
    ChapterTasteGate HausdorffCompletionFilterSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionFilterSeparationFromEventFlow
        (hausdorffCompletionFilterSeparationToEventFlow x) = some x
    exact hausdorffCompletionFilterSeparation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffCompletionFilterSeparationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HausdorffCompletionFilterSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffCompletionFilterSeparationChapterTasteGate

theorem HausdorffCompletionFilterSeparationTasteGate_single_carrier_alignment :
    ∃ carrier : HausdorffCompletionFilterSeparationUp,
      hausdorffCompletionFilterSeparationFields carrier =
          [BHist.Empty, BHist.e0 BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty] ∧
        hausdorffCompletionFilterSeparationEncodeBHist (BHist.e0 BHist.Empty) =
          [BMark.b0] ∧
          hausdorffCompletionFilterSeparationFromEventFlow
              (hausdorffCompletionFilterSeparationToEventFlow carrier) =
            some carrier := by
  -- BEDC touchpoint anchor: BHist BMark
  let carrier :=
    HausdorffCompletionFilterSeparationUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  exact ⟨carrier, rfl, rfl, rfl⟩

end BEDC.Derived.HausdorffCompletionFilterSeparationUp
