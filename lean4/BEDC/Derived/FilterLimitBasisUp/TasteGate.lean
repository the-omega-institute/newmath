import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FilterLimitBasisUp : Type where
  | mk (Q F L W R D E H C P N : BHist) : FilterLimitBasisUp
  deriving DecidableEq

def filterLimitBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: filterLimitBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: filterLimitBasisEncodeBHist h

def filterLimitBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (filterLimitBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (filterLimitBasisDecodeBHist tail)

private theorem filterLimitBasisDecode_encode_bhist :
    ∀ h : BHist, filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def filterLimitBasisFields : FilterLimitBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FilterLimitBasisUp.mk Q F L W R D E H C P N => [Q, F, L, W, R, D, E, H, C, P, N]

def filterLimitBasisToEventFlow : FilterLimitBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (filterLimitBasisFields x).map filterLimitBasisEncodeBHist

private def filterLimitBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => filterLimitBasisEventAtDefault index rest

def filterLimitBasisFromEventFlow (ef : EventFlow) : Option FilterLimitBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FilterLimitBasisUp.mk
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 0 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 1 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 2 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 3 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 4 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 5 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 6 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 7 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 8 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 9 ef))
      (filterLimitBasisDecodeBHist (filterLimitBasisEventAtDefault 10 ef)))

private theorem filterLimitBasis_round_trip :
    ∀ x : FilterLimitBasisUp,
      filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q F L W R D E H C P N =>
      change
        some
          (FilterLimitBasisUp.mk
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist Q))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist F))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist L))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist W))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist R))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist D))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist E))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist H))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist C))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist P))
            (filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist N))) =
          some (FilterLimitBasisUp.mk Q F L W R D E H C P N)
      rw [filterLimitBasisDecode_encode_bhist Q, filterLimitBasisDecode_encode_bhist F,
        filterLimitBasisDecode_encode_bhist L, filterLimitBasisDecode_encode_bhist W,
        filterLimitBasisDecode_encode_bhist R, filterLimitBasisDecode_encode_bhist D,
        filterLimitBasisDecode_encode_bhist E, filterLimitBasisDecode_encode_bhist H,
        filterLimitBasisDecode_encode_bhist C, filterLimitBasisDecode_encode_bhist P,
        filterLimitBasisDecode_encode_bhist N]

private theorem filterLimitBasisToEventFlow_injective {x y : FilterLimitBasisUp} :
    filterLimitBasisToEventFlow x = filterLimitBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) =
        filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow y) :=
    congrArg filterLimitBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (filterLimitBasis_round_trip x).symm
      (Eq.trans hread (filterLimitBasis_round_trip y)))

instance filterLimitBasisBHistCarrier : BHistCarrier FilterLimitBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := filterLimitBasisToEventFlow
  fromEventFlow := filterLimitBasisFromEventFlow

instance filterLimitBasisChapterTasteGate : ChapterTasteGate FilterLimitBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change filterLimitBasisFromEventFlow (filterLimitBasisToEventFlow x) = some x
    exact filterLimitBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (filterLimitBasisToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FilterLimitBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  filterLimitBasisChapterTasteGate

theorem FilterLimitBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, filterLimitBasisDecodeBHist (filterLimitBasisEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FilterLimitBasisUp) ∧
        Nonempty (ChapterTasteGate FilterLimitBasisUp) ∧
          filterLimitBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨filterLimitBasisDecode_encode_bhist,
      Nonempty.intro filterLimitBasisBHistCarrier,
      Nonempty.intro filterLimitBasisChapterTasteGate,
      rfl⟩

end BEDC.Derived.FilterLimitBasisUp
