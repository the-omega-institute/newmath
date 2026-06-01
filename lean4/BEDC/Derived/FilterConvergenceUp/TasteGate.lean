import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterConvergenceUp : Type where
  | mk (B X T V E H C P N : BHist) : FilterConvergenceUp
  deriving DecidableEq

def filterConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterConvergenceEncodeBHist h

def filterConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterConvergenceDecodeBHist tail)

private theorem filterConvergenceDecode_encode_bhist :
    ∀ h : BHist,
      filterConvergenceDecodeBHist (filterConvergenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterConvergenceFields : FilterConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterConvergenceUp.mk B X T V E H C P N => [B, X, T, V, E, H, C, P, N]

def filterConvergenceToEventFlow : FilterConvergenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterConvergenceFields x).map filterConvergenceEncodeBHist

private def filterConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterConvergenceEventAt index rest

def filterConvergenceFromEventFlow (ef : EventFlow) : Option FilterConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterConvergenceUp.mk
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 0 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 1 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 2 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 3 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 4 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 5 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 6 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 7 ef))
      (filterConvergenceDecodeBHist (filterConvergenceEventAt 8 ef)))

private theorem filterConvergence_round_trip
    (x : FilterConvergenceUp) :
    filterConvergenceFromEventFlow (filterConvergenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B X T V E H C P N =>
      change
        some
          (FilterConvergenceUp.mk
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist B))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist X))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist T))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist V))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist E))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist H))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist C))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist P))
            (filterConvergenceDecodeBHist (filterConvergenceEncodeBHist N))) =
          some (FilterConvergenceUp.mk B X T V E H C P N)
      rw [filterConvergenceDecode_encode_bhist B,
        filterConvergenceDecode_encode_bhist X,
        filterConvergenceDecode_encode_bhist T,
        filterConvergenceDecode_encode_bhist V,
        filterConvergenceDecode_encode_bhist E,
        filterConvergenceDecode_encode_bhist H,
        filterConvergenceDecode_encode_bhist C,
        filterConvergenceDecode_encode_bhist P,
        filterConvergenceDecode_encode_bhist N]

private theorem filterConvergenceToEventFlow_injective
    {x y : FilterConvergenceUp} :
    filterConvergenceToEventFlow x = filterConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterConvergenceFromEventFlow (filterConvergenceToEventFlow x) =
        filterConvergenceFromEventFlow (filterConvergenceToEventFlow y) :=
    congrArg filterConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (filterConvergence_round_trip x).symm
      (Eq.trans hread (filterConvergence_round_trip y)))

private theorem filterConvergence_field_faithful :
    ∀ x y : FilterConvergenceUp,
      filterConvergenceFields x = filterConvergenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 X1 T1 V1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 X2 T2 V2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance filterConvergenceBHistCarrier : BHistCarrier FilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterConvergenceToEventFlow
  fromEventFlow := filterConvergenceFromEventFlow

instance filterConvergenceChapterTasteGate :
    ChapterTasteGate FilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      filterConvergenceFromEventFlow (filterConvergenceToEventFlow x) =
        some x
    exact filterConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (filterConvergenceToEventFlow_injective heq)

instance filterConvergenceFieldFaithful : FieldFaithful FilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := filterConvergenceFields
  field_faithful := filterConvergence_field_faithful

instance filterConvergenceNontrivial : Nontrivial FilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FilterConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FilterConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FilterConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterConvergenceChapterTasteGate

theorem FilterConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, filterConvergenceDecodeBHist (filterConvergenceEncodeBHist h) = h) ∧
      (∀ x : FilterConvergenceUp,
        filterConvergenceFromEventFlow (filterConvergenceToEventFlow x) = some x) ∧
        (∀ x y : FilterConvergenceUp,
          filterConvergenceToEventFlow x = filterConvergenceToEventFlow y → x = y) ∧
          filterConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow BHistCarrier ChapterTasteGate
  exact
    ⟨filterConvergenceDecode_encode_bhist,
      filterConvergence_round_trip,
      (fun _ _ heq => filterConvergenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FilterConvergenceUp
