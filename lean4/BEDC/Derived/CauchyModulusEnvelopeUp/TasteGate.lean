import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusEnvelopeUp : Type where
  | mk (D W R F M U S H C P N : BHist) : CauchyModulusEnvelopeUp
  deriving DecidableEq

def cauchyModulusEnvelopeFields : CauchyModulusEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusEnvelopeUp.mk D W R F M U S H C P N =>
      [D, W, R, F, M, U, S, H, C, P, N]

def cauchyModulusEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusEnvelopeEncodeBHist h

def cauchyModulusEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusEnvelopeDecodeBHist tail)

private theorem CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyModulusEnvelopeToEventFlow : CauchyModulusEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusEnvelopeFields x).map cauchyModulusEnvelopeEncodeBHist

private def cauchyModulusEnvelopeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusEnvelopeEventAtDefault index rest

def cauchyModulusEnvelopeFromEventFlow (ef : EventFlow) :
    Option CauchyModulusEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusEnvelopeUp.mk
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 0 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 1 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 2 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 3 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 4 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 5 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 6 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 7 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 8 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 9 ef))
      (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEventAtDefault 10 ef)))

private theorem CauchyModulusEnvelopeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusEnvelopeUp,
      cauchyModulusEnvelopeFromEventFlow
        (cauchyModulusEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R F M U S H C P N =>
      change
        some
          (CauchyModulusEnvelopeUp.mk
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist D))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist W))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist R))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist F))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist M))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist U))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist S))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist H))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist C))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist P))
            (cauchyModulusEnvelopeDecodeBHist (cauchyModulusEnvelopeEncodeBHist N))) =
          some (CauchyModulusEnvelopeUp.mk D W R F M U S H C P N)
      rw [CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode W,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode F,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode M,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode U,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode S,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusEnvelopeUp} :
    cauchyModulusEnvelopeToEventFlow x = cauchyModulusEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusEnvelopeFromEventFlow (cauchyModulusEnvelopeToEventFlow x) =
        cauchyModulusEnvelopeFromEventFlow (cauchyModulusEnvelopeToEventFlow y) :=
    congrArg cauchyModulusEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusEnvelopeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusEnvelopeTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyModulusEnvelopeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyModulusEnvelopeUp,
      cauchyModulusEnvelopeFields x = cauchyModulusEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ R₁ F₁ M₁ U₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ R₂ F₂ M₂ U₂ S₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hD t0
          injection t0 with hW t1
          injection t1 with hR t2
          injection t2 with hF t3
          injection t3 with hM t4
          injection t4 with hU t5
          injection t5 with hS t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hD
          subst hW
          subst hR
          subst hF
          subst hM
          subst hU
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyModulusEnvelopeBHistCarrier : BHistCarrier CauchyModulusEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusEnvelopeToEventFlow
  fromEventFlow := cauchyModulusEnvelopeFromEventFlow

instance cauchyModulusEnvelopeChapterTasteGate :
    ChapterTasteGate CauchyModulusEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusEnvelopeFromEventFlow (cauchyModulusEnvelopeToEventFlow x) = some x
    exact CauchyModulusEnvelopeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyModulusEnvelopeFieldFaithful :
    FieldFaithful CauchyModulusEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusEnvelopeFields
  field_faithful := CauchyModulusEnvelopeTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate CauchyModulusEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusEnvelopeChapterTasteGate

theorem CauchyModulusEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyModulusEnvelopeUp) ∧
      Nonempty (ChapterTasteGate CauchyModulusEnvelopeUp) ∧
        Nonempty (FieldFaithful CauchyModulusEnvelopeUp) ∧
          cauchyModulusEnvelopeEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            (∀ h : BHist,
              cauchyModulusEnvelopeDecodeBHist
                (cauchyModulusEnvelopeEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro cauchyModulusEnvelopeBHistCarrier,
      Nonempty.intro cauchyModulusEnvelopeChapterTasteGate,
      Nonempty.intro cauchyModulusEnvelopeFieldFaithful,
      rfl,
      CauchyModulusEnvelopeTasteGate_single_carrier_alignment_decode_encode⟩

end BEDC.Derived.CauchyModulusEnvelopeUp
