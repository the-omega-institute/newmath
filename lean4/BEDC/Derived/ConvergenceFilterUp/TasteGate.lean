import BEDC.Derived.ConvergenceFilterUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvergenceFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def convergenceFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convergenceFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convergenceFilterEncodeBHist h

def convergenceFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convergenceFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convergenceFilterDecodeBHist tail)

private theorem ConvergenceFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, convergenceFilterDecodeBHist (convergenceFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def convergenceFilterFields : ConvergenceFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConvergenceFilterUp.mk filterBase neighbourhood limitPoint window readback realSeal
      transport replay provenance name =>
      [filterBase, neighbourhood, limitPoint, window, readback, realSeal, transport,
        replay, provenance, name]

def convergenceFilterToEventFlow : ConvergenceFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (convergenceFilterFields x).map convergenceFilterEncodeBHist

private def convergenceFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => convergenceFilterEventAtDefault index rest

def convergenceFilterFromEventFlow (ef : EventFlow) : Option ConvergenceFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConvergenceFilterUp.mk
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 0 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 1 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 2 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 3 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 4 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 5 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 6 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 7 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 8 ef))
      (convergenceFilterDecodeBHist (convergenceFilterEventAtDefault 9 ef)))

private theorem ConvergenceFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConvergenceFilterUp,
      convergenceFilterFromEventFlow (convergenceFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filterBase neighbourhood limitPoint window readback realSeal transport replay
      provenance name =>
      change
        some
          (ConvergenceFilterUp.mk
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist filterBase))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist neighbourhood))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist limitPoint))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist window))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist readback))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist realSeal))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist transport))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist replay))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist provenance))
            (convergenceFilterDecodeBHist (convergenceFilterEncodeBHist name))) =
          some
            (ConvergenceFilterUp.mk filterBase neighbourhood limitPoint window readback
              realSeal transport replay provenance name)
      rw [ConvergenceFilterTasteGate_single_carrier_alignment_decode filterBase,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode neighbourhood,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode limitPoint,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode window,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode readback,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode realSeal,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode transport,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode replay,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode provenance,
        ConvergenceFilterTasteGate_single_carrier_alignment_decode name]

private theorem convergenceFilterToEventFlow_injective {x y : ConvergenceFilterUp} :
    convergenceFilterToEventFlow x = convergenceFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convergenceFilterFromEventFlow (convergenceFilterToEventFlow x) =
        convergenceFilterFromEventFlow (convergenceFilterToEventFlow y) :=
    congrArg convergenceFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConvergenceFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConvergenceFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem convergenceFilter_fields_faithful :
    ∀ x y : ConvergenceFilterUp,
      convergenceFilterFields x = convergenceFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk f1 nb1 x1 w1 r1 e1 h1 c1 p1 n1 =>
      cases y with
      | mk f2 nb2 x2 w2 r2 e2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance convergenceFilterBHistCarrier : BHistCarrier ConvergenceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convergenceFilterToEventFlow
  fromEventFlow := convergenceFilterFromEventFlow

instance convergenceFilterChapterTasteGate : ChapterTasteGate ConvergenceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change convergenceFilterFromEventFlow (convergenceFilterToEventFlow x) = some x
    exact ConvergenceFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (convergenceFilterToEventFlow_injective heq)

instance convergenceFilterFieldFaithful : FieldFaithful ConvergenceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := convergenceFilterFields
  field_faithful := convergenceFilter_fields_faithful

instance convergenceFilterNontrivial : Nontrivial ConvergenceFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConvergenceFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ConvergenceFilterUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def convergenceFilterTasteGate : ChapterTasteGate ConvergenceFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  convergenceFilterChapterTasteGate

theorem ConvergenceFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, convergenceFilterDecodeBHist (convergenceFilterEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.ConvergenceFilterUp,
        convergenceFilterFromEventFlow (convergenceFilterToEventFlow x) = some x) ∧
        (∀ x y : BEDC.Derived.ConvergenceFilterUp,
          convergenceFilterToEventFlow x = convergenceFilterToEventFlow y → x = y) ∧
          convergenceFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate FieldFaithful
  exact
    ⟨ConvergenceFilterTasteGate_single_carrier_alignment_decode,
      ConvergenceFilterTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => convergenceFilterToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ConvergenceFilterUp
