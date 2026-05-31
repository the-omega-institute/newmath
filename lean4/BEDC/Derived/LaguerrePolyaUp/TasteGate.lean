import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LaguerrePolyaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LaguerrePolyaUp : Type where
  | mk (A B R S Q W E T H C P N : BHist) : LaguerrePolyaUp
  deriving DecidableEq

def laguerrePolyaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: laguerrePolyaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: laguerrePolyaEncodeBHist h

def laguerrePolyaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (laguerrePolyaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (laguerrePolyaDecodeBHist tail)

private theorem LaguerrePolyaTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def laguerrePolyaFields : LaguerrePolyaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LaguerrePolyaUp.mk A B R S Q W E T H C P N => [A, B, R, S, Q, W, E, T, H, C, P, N]

def laguerrePolyaToEventFlow : LaguerrePolyaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (laguerrePolyaFields x).map laguerrePolyaEncodeBHist

private def laguerrePolyaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => laguerrePolyaEventAtDefault index rest

def laguerrePolyaFromEventFlow (ef : EventFlow) : Option LaguerrePolyaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LaguerrePolyaUp.mk
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 0 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 1 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 2 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 3 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 4 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 5 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 6 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 7 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 8 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 9 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 10 ef))
      (laguerrePolyaDecodeBHist (laguerrePolyaEventAtDefault 11 ef)))

private theorem LaguerrePolyaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LaguerrePolyaUp,
      laguerrePolyaFromEventFlow (laguerrePolyaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B R S Q W E T H C P N =>
      change
        some
          (LaguerrePolyaUp.mk
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist A))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist B))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist R))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist S))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist Q))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist W))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist E))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist T))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist H))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist C))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist P))
            (laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist N))) =
          some (LaguerrePolyaUp.mk A B R S Q W E T H C P N)
      rw [LaguerrePolyaTasteGate_single_carrier_alignment_decode A,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode B,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode R,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode S,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode Q,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode W,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode E,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode T,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode H,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode C,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode P,
        LaguerrePolyaTasteGate_single_carrier_alignment_decode N]

private theorem LaguerrePolyaTasteGate_single_carrier_alignment_injective
    {x y : LaguerrePolyaUp} :
    laguerrePolyaToEventFlow x = laguerrePolyaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      laguerrePolyaFromEventFlow (laguerrePolyaToEventFlow x) =
        laguerrePolyaFromEventFlow (laguerrePolyaToEventFlow y) :=
    congrArg laguerrePolyaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LaguerrePolyaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LaguerrePolyaTasteGate_single_carrier_alignment_round_trip y)))

private theorem laguerrePolyaFields_faithful :
    ∀ x y : LaguerrePolyaUp, laguerrePolyaFields x = laguerrePolyaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ R₁ S₁ Q₁ W₁ E₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ R₂ S₂ Q₂ W₂ E₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance laguerrePolyaBHistCarrier : BHistCarrier LaguerrePolyaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := laguerrePolyaToEventFlow
  fromEventFlow := laguerrePolyaFromEventFlow

instance laguerrePolyaChapterTasteGate : ChapterTasteGate LaguerrePolyaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change laguerrePolyaFromEventFlow (laguerrePolyaToEventFlow x) = some x
    exact LaguerrePolyaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LaguerrePolyaTasteGate_single_carrier_alignment_injective heq)

instance laguerrePolyaFieldFaithful : FieldFaithful LaguerrePolyaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := laguerrePolyaFields
  field_faithful := laguerrePolyaFields_faithful

instance laguerrePolyaNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LaguerrePolyaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LaguerrePolyaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LaguerrePolyaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def laguerrePolyaTasteGate : ChapterTasteGate LaguerrePolyaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  laguerrePolyaChapterTasteGate

theorem LaguerrePolyaTasteGate_single_carrier_alignment :
    (∀ h : BHist, laguerrePolyaDecodeBHist (laguerrePolyaEncodeBHist h) = h) ∧
      (∀ x : LaguerrePolyaUp,
        laguerrePolyaFromEventFlow (laguerrePolyaToEventFlow x) = some x) ∧
      (∀ x y : LaguerrePolyaUp,
        laguerrePolyaToEventFlow x = laguerrePolyaToEventFlow y → x = y) ∧
      laguerrePolyaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact LaguerrePolyaTasteGate_single_carrier_alignment_decode
  constructor
  · exact LaguerrePolyaTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact LaguerrePolyaTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.LaguerrePolyaUp
