import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactLocatedIntervalSubcoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactLocatedIntervalSubcoverUp : Type where
  | mk (I N C M E H R P L : BHist) : CompactLocatedIntervalSubcoverUp
  deriving DecidableEq

def compactLocatedIntervalSubcoverEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactLocatedIntervalSubcoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactLocatedIntervalSubcoverEncodeBHist h

def compactLocatedIntervalSubcoverDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactLocatedIntervalSubcoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactLocatedIntervalSubcoverDecodeBHist tail)

private theorem compactLocatedIntervalSubcoverDecode_encode :
    forall h : BHist,
      compactLocatedIntervalSubcoverDecodeBHist
        (compactLocatedIntervalSubcoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactLocatedIntervalSubcoverFields :
    CompactLocatedIntervalSubcoverUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactLocatedIntervalSubcoverUp.mk I N C M E H R P L => [I, N, C, M, E, H, R, P, L]

def compactLocatedIntervalSubcoverToEventFlow :
    CompactLocatedIntervalSubcoverUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactLocatedIntervalSubcoverFields x).map compactLocatedIntervalSubcoverEncodeBHist

private def compactLocatedIntervalSubcoverEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactLocatedIntervalSubcoverEventAt index rest

def compactLocatedIntervalSubcoverFromEventFlow :
    EventFlow -> Option CompactLocatedIntervalSubcoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactLocatedIntervalSubcoverUp.mk
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 0 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 1 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 2 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 3 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 4 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 5 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 6 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 7 ef))
        (compactLocatedIntervalSubcoverDecodeBHist (compactLocatedIntervalSubcoverEventAt 8 ef)))

private theorem compactLocatedIntervalSubcover_round_trip :
    forall x : CompactLocatedIntervalSubcoverUp,
      compactLocatedIntervalSubcoverFromEventFlow
        (compactLocatedIntervalSubcoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I N C M E H R P L =>
      change
        some
            (CompactLocatedIntervalSubcoverUp.mk
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist I))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist N))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist C))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist M))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist E))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist H))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist R))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist P))
              (compactLocatedIntervalSubcoverDecodeBHist
                (compactLocatedIntervalSubcoverEncodeBHist L))) =
          some (CompactLocatedIntervalSubcoverUp.mk I N C M E H R P L)
      rw [compactLocatedIntervalSubcoverDecode_encode I,
        compactLocatedIntervalSubcoverDecode_encode N,
        compactLocatedIntervalSubcoverDecode_encode C,
        compactLocatedIntervalSubcoverDecode_encode M,
        compactLocatedIntervalSubcoverDecode_encode E,
        compactLocatedIntervalSubcoverDecode_encode H,
        compactLocatedIntervalSubcoverDecode_encode R,
        compactLocatedIntervalSubcoverDecode_encode P,
        compactLocatedIntervalSubcoverDecode_encode L]

private theorem compactLocatedIntervalSubcoverToEventFlow_injective
    {x y : CompactLocatedIntervalSubcoverUp} :
    compactLocatedIntervalSubcoverToEventFlow x =
      compactLocatedIntervalSubcoverToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactLocatedIntervalSubcoverFromEventFlow
          (compactLocatedIntervalSubcoverToEventFlow x) =
        compactLocatedIntervalSubcoverFromEventFlow
          (compactLocatedIntervalSubcoverToEventFlow y) :=
    congrArg compactLocatedIntervalSubcoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactLocatedIntervalSubcover_round_trip x).symm
      (Eq.trans hread (compactLocatedIntervalSubcover_round_trip y)))

private theorem compactLocatedIntervalSubcover_field_faithful :
    forall x y : CompactLocatedIntervalSubcoverUp,
      compactLocatedIntervalSubcoverFields x =
        compactLocatedIntervalSubcoverFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 N1 C1 M1 E1 H1 R1 P1 L1 =>
      cases y with
      | mk I2 N2 C2 M2 E2 H2 R2 P2 L2 =>
          cases hfields
          rfl

instance compactLocatedIntervalSubcoverBHistCarrier :
    BHistCarrier CompactLocatedIntervalSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactLocatedIntervalSubcoverToEventFlow
  fromEventFlow := compactLocatedIntervalSubcoverFromEventFlow

instance compactLocatedIntervalSubcoverChapterTasteGate :
    ChapterTasteGate CompactLocatedIntervalSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactLocatedIntervalSubcoverFromEventFlow
        (compactLocatedIntervalSubcoverToEventFlow x) = some x
    exact compactLocatedIntervalSubcover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactLocatedIntervalSubcoverToEventFlow_injective heq)

instance compactLocatedIntervalSubcoverFieldFaithful :
    FieldFaithful CompactLocatedIntervalSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactLocatedIntervalSubcoverFields
  field_faithful := compactLocatedIntervalSubcover_field_faithful

instance compactLocatedIntervalSubcoverNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactLocatedIntervalSubcoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactLocatedIntervalSubcoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactLocatedIntervalSubcoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactLocatedIntervalSubcoverTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactLocatedIntervalSubcoverUp) ∧
      Nonempty (FieldFaithful CompactLocatedIntervalSubcoverUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactLocatedIntervalSubcoverUp) ∧
      (forall h : BHist,
        compactLocatedIntervalSubcoverDecodeBHist
          (compactLocatedIntervalSubcoverEncodeBHist h) = h) ∧
      (forall x : CompactLocatedIntervalSubcoverUp,
        compactLocatedIntervalSubcoverFromEventFlow
          (compactLocatedIntervalSubcoverToEventFlow x) = some x) ∧
      (forall x y : CompactLocatedIntervalSubcoverUp,
        compactLocatedIntervalSubcoverToEventFlow x =
          compactLocatedIntervalSubcoverToEventFlow y -> x = y) ∧
      compactLocatedIntervalSubcoverEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨compactLocatedIntervalSubcoverChapterTasteGate⟩
  constructor
  · exact ⟨compactLocatedIntervalSubcoverFieldFaithful⟩
  constructor
  · exact ⟨compactLocatedIntervalSubcoverNontrivial⟩
  constructor
  · exact compactLocatedIntervalSubcoverDecode_encode
  constructor
  · exact compactLocatedIntervalSubcover_round_trip
  constructor
  · intro x y heq
    exact compactLocatedIntervalSubcoverToEventFlow_injective heq
  · rfl

end BEDC.Derived.CompactLocatedIntervalSubcoverUp
