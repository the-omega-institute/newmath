import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationalEquationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationalEquationUp : Type where
  | mk (B D L T U H C P N : BHist) : VariationalEquationUp
  deriving DecidableEq

def variationalEquationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationalEquationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationalEquationEncodeBHist h

def variationalEquationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationalEquationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationalEquationDecodeBHist tail)

private theorem VariationalEquationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, variationalEquationDecodeBHist (variationalEquationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationalEquationFields : VariationalEquationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationalEquationUp.mk B D L T U H C P N => [B, D, L, T, U, H, C, P, N]

def variationalEquationToEventFlow : VariationalEquationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (variationalEquationFields x).map variationalEquationEncodeBHist

private def variationalEquationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => variationalEquationEventAtDefault index rest

def variationalEquationFromEventFlow (ef : EventFlow) : Option VariationalEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VariationalEquationUp.mk
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 0 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 1 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 2 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 3 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 4 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 5 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 6 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 7 ef))
      (variationalEquationDecodeBHist (variationalEquationEventAtDefault 8 ef)))

private theorem VariationalEquationTasteGate_single_carrier_alignment_round_trip
    (x : VariationalEquationUp) :
    variationalEquationFromEventFlow (variationalEquationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B D L T U H C P N =>
      change
        some
          (VariationalEquationUp.mk
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist B))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist D))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist L))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist T))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist U))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist H))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist C))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist P))
            (variationalEquationDecodeBHist (variationalEquationEncodeBHist N))) =
          some (VariationalEquationUp.mk B D L T U H C P N)
      rw [VariationalEquationTasteGate_single_carrier_alignment_decode B,
        VariationalEquationTasteGate_single_carrier_alignment_decode D,
        VariationalEquationTasteGate_single_carrier_alignment_decode L,
        VariationalEquationTasteGate_single_carrier_alignment_decode T,
        VariationalEquationTasteGate_single_carrier_alignment_decode U,
        VariationalEquationTasteGate_single_carrier_alignment_decode H,
        VariationalEquationTasteGate_single_carrier_alignment_decode C,
        VariationalEquationTasteGate_single_carrier_alignment_decode P,
        VariationalEquationTasteGate_single_carrier_alignment_decode N]

private theorem VariationalEquationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VariationalEquationUp} :
    variationalEquationToEventFlow x = variationalEquationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationalEquationFromEventFlow (variationalEquationToEventFlow x) =
        variationalEquationFromEventFlow (variationalEquationToEventFlow y) :=
    congrArg variationalEquationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (VariationalEquationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (VariationalEquationTasteGate_single_carrier_alignment_round_trip y)))

instance variationalEquationBHistCarrier : BHistCarrier VariationalEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationalEquationToEventFlow
  fromEventFlow := variationalEquationFromEventFlow

instance variationalEquationChapterTasteGate : ChapterTasteGate VariationalEquationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationalEquationFromEventFlow (variationalEquationToEventFlow x) = some x
    exact VariationalEquationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VariationalEquationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate VariationalEquationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  variationalEquationChapterTasteGate

theorem VariationalEquationTasteGate_single_carrier_alignment :
    (∀ h : BHist, variationalEquationDecodeBHist (variationalEquationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VariationalEquationUp) ∧
        Nonempty (ChapterTasteGate VariationalEquationUp) ∧
          variationalEquationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨VariationalEquationTasteGate_single_carrier_alignment_decode,
      ⟨variationalEquationBHistCarrier⟩,
      ⟨variationalEquationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.VariationalEquationUp
