import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SimplicialApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SimplicialApproximationUp : Type where
  | mk (K L S V F T B M H C P N : BHist) : SimplicialApproximationUp
  deriving DecidableEq

def simplicialApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: simplicialApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: simplicialApproximationEncodeBHist h

def simplicialApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (simplicialApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (simplicialApproximationDecodeBHist tail)

private theorem SimplicialApproximationUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def simplicialApproximationFields : SimplicialApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SimplicialApproximationUp.mk K L S V F T B M H C P N =>
      [K, L, S, V, F, T, B, M, H, C, P, N]

def simplicialApproximationToEventFlow : SimplicialApproximationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (simplicialApproximationFields x).map simplicialApproximationEncodeBHist

private def simplicialApproximationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => simplicialApproximationEventAtDefault index rest

def simplicialApproximationFromEventFlow (ef : EventFlow) : Option SimplicialApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SimplicialApproximationUp.mk
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 0 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 1 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 2 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 3 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 4 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 5 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 6 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 7 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 8 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 9 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 10 ef))
      (simplicialApproximationDecodeBHist (simplicialApproximationEventAtDefault 11 ef)))

private theorem SimplicialApproximationUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SimplicialApproximationUp,
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K L S V F T B M H C P N =>
      change
        some
            (SimplicialApproximationUp.mk
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist K))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist L))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist S))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist V))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist F))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist T))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist B))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist M))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist H))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist C))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist P))
              (simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist N))) =
          some (SimplicialApproximationUp.mk K L S V F T B M H C P N)
      rw [SimplicialApproximationUpTasteGate_single_carrier_alignment_decode K,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode L,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode S,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode V,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode F,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode T,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode B,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode M,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode H,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode C,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode P,
        SimplicialApproximationUpTasteGate_single_carrier_alignment_decode N]

private theorem SimplicialApproximationUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SimplicialApproximationUp} :
    simplicialApproximationToEventFlow x = simplicialApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
        simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow y) :=
    congrArg simplicialApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SimplicialApproximationUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SimplicialApproximationUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem SimplicialApproximationUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : SimplicialApproximationUp,
      simplicialApproximationFields x = simplicialApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 L1 S1 V1 F1 T1 B1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 L2 S2 V2 F2 T2 B2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance simplicialApproximationBHistCarrier : BHistCarrier SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := simplicialApproximationToEventFlow
  fromEventFlow := simplicialApproximationFromEventFlow

instance simplicialApproximationChapterTasteGate :
    ChapterTasteGate SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
      some x
    exact SimplicialApproximationUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SimplicialApproximationUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance simplicialApproximationFieldFaithful : FieldFaithful SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := simplicialApproximationFields
  field_faithful := SimplicialApproximationUpTasteGate_single_carrier_alignment_fields

instance simplicialApproximationNontrivial : Nontrivial SimplicialApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SimplicialApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SimplicialApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SimplicialApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  simplicialApproximationChapterTasteGate

theorem SimplicialApproximationUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      simplicialApproximationDecodeBHist (simplicialApproximationEncodeBHist h) = h) ∧
      (∀ x : SimplicialApproximationUp,
        simplicialApproximationFromEventFlow (simplicialApproximationToEventFlow x) =
          some x) ∧
        (∀ x y : SimplicialApproximationUp,
          simplicialApproximationToEventFlow x = simplicialApproximationToEventFlow y →
            x = y) ∧
          simplicialApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SimplicialApproximationUpTasteGate_single_carrier_alignment_decode,
      SimplicialApproximationUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SimplicialApproximationUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SimplicialApproximationUp
