import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetFilterUp : Type where
  | mk (U T S M B Q R A H C P N : BHist) : FrechetFilterUp
  deriving DecidableEq

def frechetFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetFilterEncodeBHist h

def frechetFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetFilterDecodeBHist tail)

private theorem FrechetFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frechetFilterDecodeBHist (frechetFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetFilterFields : FrechetFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetFilterUp.mk U T S M B Q R A H C P N => [U, T, S, M, B, Q, R, A, H, C, P, N]

def frechetFilterToEventFlow : FrechetFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (frechetFilterFields x).map frechetFilterEncodeBHist

private def frechetFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetFilterEventAtDefault index rest

def frechetFilterFromEventFlow (ef : EventFlow) : Option FrechetFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrechetFilterUp.mk
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 0 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 1 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 2 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 3 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 4 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 5 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 6 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 7 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 8 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 9 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 10 ef))
      (frechetFilterDecodeBHist (frechetFilterEventAtDefault 11 ef)))

private theorem FrechetFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrechetFilterUp,
      frechetFilterFromEventFlow (frechetFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U T S M B Q R A H C P N =>
      change
        some
          (FrechetFilterUp.mk
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist U))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist T))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist S))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist M))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist B))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist Q))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist R))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist A))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist H))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist C))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist P))
            (frechetFilterDecodeBHist (frechetFilterEncodeBHist N))) =
          some (FrechetFilterUp.mk U T S M B Q R A H C P N)
      rw [FrechetFilterTasteGate_single_carrier_alignment_decode U,
        FrechetFilterTasteGate_single_carrier_alignment_decode T,
        FrechetFilterTasteGate_single_carrier_alignment_decode S,
        FrechetFilterTasteGate_single_carrier_alignment_decode M,
        FrechetFilterTasteGate_single_carrier_alignment_decode B,
        FrechetFilterTasteGate_single_carrier_alignment_decode Q,
        FrechetFilterTasteGate_single_carrier_alignment_decode R,
        FrechetFilterTasteGate_single_carrier_alignment_decode A,
        FrechetFilterTasteGate_single_carrier_alignment_decode H,
        FrechetFilterTasteGate_single_carrier_alignment_decode C,
        FrechetFilterTasteGate_single_carrier_alignment_decode P,
        FrechetFilterTasteGate_single_carrier_alignment_decode N]

private theorem FrechetFilterTasteGate_single_carrier_alignment_injective
    {x y : FrechetFilterUp} :
    frechetFilterToEventFlow x = frechetFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetFilterFromEventFlow (frechetFilterToEventFlow x) =
        frechetFilterFromEventFlow (frechetFilterToEventFlow y) :=
    congrArg frechetFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem FrechetFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : FrechetFilterUp, frechetFilterFields x = frechetFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 T1 S1 M1 B1 Q1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 T2 S2 M2 B2 Q2 R2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance frechetFilterBHistCarrier : BHistCarrier FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetFilterToEventFlow
  fromEventFlow := frechetFilterFromEventFlow

instance frechetFilterChapterTasteGate : ChapterTasteGate FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetFilterFromEventFlow (frechetFilterToEventFlow x) = some x
    exact FrechetFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetFilterTasteGate_single_carrier_alignment_injective heq)

instance frechetFilterFieldFaithful : FieldFaithful FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := frechetFilterFields
  field_faithful := FrechetFilterTasteGate_single_carrier_alignment_fields

instance frechetFilterNontrivial : Nontrivial FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FrechetFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FrechetFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FrechetFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetFilterChapterTasteGate

theorem FrechetFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, frechetFilterDecodeBHist (frechetFilterEncodeBHist h) = h) ∧
      (∀ x : FrechetFilterUp,
        frechetFilterFromEventFlow (frechetFilterToEventFlow x) = some x) ∧
        (∀ x y : FrechetFilterUp,
          frechetFilterToEventFlow x = frechetFilterToEventFlow y → x = y) ∧
          frechetFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FrechetFilterTasteGate_single_carrier_alignment_decode,
      FrechetFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FrechetFilterTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.FrechetFilterUp
