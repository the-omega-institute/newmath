import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
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

private theorem frechetFilter_decode_encode :
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

private theorem frechetFilter_round_trip :
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
      rw [frechetFilter_decode_encode U, frechetFilter_decode_encode T,
        frechetFilter_decode_encode S, frechetFilter_decode_encode M,
        frechetFilter_decode_encode B, frechetFilter_decode_encode Q,
        frechetFilter_decode_encode R, frechetFilter_decode_encode A,
        frechetFilter_decode_encode H, frechetFilter_decode_encode C,
        frechetFilter_decode_encode P, frechetFilter_decode_encode N]

private theorem frechetFilterToEventFlow_injective {x y : FrechetFilterUp} :
    frechetFilterToEventFlow x = frechetFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetFilterFromEventFlow (frechetFilterToEventFlow x) =
        frechetFilterFromEventFlow (frechetFilterToEventFlow y) :=
    congrArg frechetFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (frechetFilter_round_trip x).symm
      (Eq.trans hread (frechetFilter_round_trip y)))

private theorem frechetFilter_fields_faithful :
    ∀ x y : FrechetFilterUp, frechetFilterFields x = frechetFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ T₁ S₁ M₁ B₁ Q₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ T₂ S₂ M₂ B₂ Q₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
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
    exact frechetFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (frechetFilterToEventFlow_injective heq)

instance frechetFilterFieldFaithful : FieldFaithful FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := frechetFilterFields
  field_faithful := frechetFilter_fields_faithful

instance frechetFilterNontrivial : BEDC.Meta.TasteGate.Nontrivial FrechetFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FrechetFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FrechetFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FrechetFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetFilterChapterTasteGate

end BEDC.Derived.FrechetFilterUp
