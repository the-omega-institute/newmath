import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WindowCoverageTriggerAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WindowCoverageTriggerAlgebraUp : Type where
  | mk (T C F L R A H Q P N : BHist) : WindowCoverageTriggerAlgebraUp
  deriving DecidableEq

def windowCoverageTriggerAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: windowCoverageTriggerAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: windowCoverageTriggerAlgebraEncodeBHist h

def windowCoverageTriggerAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (windowCoverageTriggerAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (windowCoverageTriggerAlgebraDecodeBHist tail)

private theorem WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEncodeBHist h) =
          h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def windowCoverageTriggerAlgebraFields :
    WindowCoverageTriggerAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WindowCoverageTriggerAlgebraUp.mk T C F L R A H Q P N =>
      [T, C, F, L, R, A, H, Q, P, N]

def windowCoverageTriggerAlgebraToEventFlow :
    WindowCoverageTriggerAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (windowCoverageTriggerAlgebraFields x).map
      windowCoverageTriggerAlgebraEncodeBHist

private def windowCoverageTriggerAlgebraEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      windowCoverageTriggerAlgebraEventAtDefault index rest

def windowCoverageTriggerAlgebraFromEventFlow
    (ef : EventFlow) : Option WindowCoverageTriggerAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WindowCoverageTriggerAlgebraUp.mk
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 0 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 1 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 2 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 3 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 4 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 5 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 6 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 7 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 8 ef))
      (windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEventAtDefault 9 ef)))

private theorem WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_round_trip
    (x : WindowCoverageTriggerAlgebraUp) :
    windowCoverageTriggerAlgebraFromEventFlow
      (windowCoverageTriggerAlgebraToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T C F L R A H Q P N =>
      change
        some
          (WindowCoverageTriggerAlgebraUp.mk
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist T))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist C))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist F))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist L))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist R))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist A))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist H))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist Q))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist P))
            (windowCoverageTriggerAlgebraDecodeBHist
              (windowCoverageTriggerAlgebraEncodeBHist N))) =
          some (WindowCoverageTriggerAlgebraUp.mk T C F L R A H Q P N)
      rw [WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode T,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode C,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode F,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode L,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode R,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode A,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode H,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode Q,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode P,
        WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode N]

private theorem WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_injective
    {x y : WindowCoverageTriggerAlgebraUp} :
    windowCoverageTriggerAlgebraToEventFlow x =
      windowCoverageTriggerAlgebraToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      windowCoverageTriggerAlgebraFromEventFlow
          (windowCoverageTriggerAlgebraToEventFlow x) =
        windowCoverageTriggerAlgebraFromEventFlow
          (windowCoverageTriggerAlgebraToEventFlow y) :=
    congrArg windowCoverageTriggerAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_round_trip y)))

private theorem WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_fields :
    ∀ x y : WindowCoverageTriggerAlgebraUp,
      windowCoverageTriggerAlgebraFields x =
        windowCoverageTriggerAlgebraFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ C₁ F₁ L₁ R₁ A₁ H₁ Q₁ P₁ N₁ =>
      cases y with
      | mk T₂ C₂ F₂ L₂ R₂ A₂ H₂ Q₂ P₂ N₂ =>
          cases hfields
          rfl

instance windowCoverageTriggerAlgebraBHistCarrier :
    BHistCarrier WindowCoverageTriggerAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := windowCoverageTriggerAlgebraToEventFlow
  fromEventFlow := windowCoverageTriggerAlgebraFromEventFlow

instance windowCoverageTriggerAlgebraChapterTasteGate :
    ChapterTasteGate WindowCoverageTriggerAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      windowCoverageTriggerAlgebraFromEventFlow
        (windowCoverageTriggerAlgebraToEventFlow x) = some x
    exact WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_injective heq)

instance windowCoverageTriggerAlgebraFieldFaithful :
    FieldFaithful WindowCoverageTriggerAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := windowCoverageTriggerAlgebraFields
  field_faithful :=
    WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_fields

instance windowCoverageTriggerAlgebraNontrivial :
    BEDC.Meta.TasteGate.Nontrivial WindowCoverageTriggerAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WindowCoverageTriggerAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      WindowCoverageTriggerAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate WindowCoverageTriggerAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  windowCoverageTriggerAlgebraChapterTasteGate

theorem WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      windowCoverageTriggerAlgebraDecodeBHist
        (windowCoverageTriggerAlgebraEncodeBHist h) = h) ∧
      (∀ x : WindowCoverageTriggerAlgebraUp,
        windowCoverageTriggerAlgebraFromEventFlow
          (windowCoverageTriggerAlgebraToEventFlow x) =
            some x) ∧
        (∀ x y : WindowCoverageTriggerAlgebraUp,
          windowCoverageTriggerAlgebraToEventFlow x =
            windowCoverageTriggerAlgebraToEventFlow y →
              x = y) ∧
          windowCoverageTriggerAlgebraEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact WindowCoverageTriggerAlgebraTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.WindowCoverageTriggerAlgebraUp
