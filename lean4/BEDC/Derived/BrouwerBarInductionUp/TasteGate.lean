import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerBarInductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerBarInductionUp : Type where
  | mk (t b m i w r e h c p n : BHist) : BrouwerBarInductionUp
  deriving DecidableEq

def brouwerBarInductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerBarInductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerBarInductionEncodeBHist h

def brouwerBarInductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerBarInductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerBarInductionDecodeBHist tail)

private theorem BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerBarInductionFields : BrouwerBarInductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerBarInductionUp.mk t b m i w r e h c p n => [t, b, m, i, w, r, e, h, c, p, n]

def brouwerBarInductionToEventFlow : BrouwerBarInductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (brouwerBarInductionFields x).map brouwerBarInductionEncodeBHist

def brouwerBarInductionFromEventFlow : EventFlow → Option BrouwerBarInductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _t :: [] => none
  | _t :: _b :: [] => none
  | _t :: _b :: _m :: [] => none
  | _t :: _b :: _m :: _i :: [] => none
  | _t :: _b :: _m :: _i :: _w :: [] => none
  | _t :: _b :: _m :: _i :: _w :: _r :: [] => none
  | _t :: _b :: _m :: _i :: _w :: _r :: _e :: [] => none
  | _t :: _b :: _m :: _i :: _w :: _r :: _e :: _h :: [] => none
  | _t :: _b :: _m :: _i :: _w :: _r :: _e :: _h :: _c :: [] => none
  | _t :: _b :: _m :: _i :: _w :: _r :: _e :: _h :: _c :: _p :: [] => none
  | t :: b :: m :: i :: w :: r :: e :: h :: c :: p :: n :: [] =>
      some
        (BrouwerBarInductionUp.mk
          (brouwerBarInductionDecodeBHist t)
          (brouwerBarInductionDecodeBHist b)
          (brouwerBarInductionDecodeBHist m)
          (brouwerBarInductionDecodeBHist i)
          (brouwerBarInductionDecodeBHist w)
          (brouwerBarInductionDecodeBHist r)
          (brouwerBarInductionDecodeBHist e)
          (brouwerBarInductionDecodeBHist h)
          (brouwerBarInductionDecodeBHist c)
          (brouwerBarInductionDecodeBHist p)
          (brouwerBarInductionDecodeBHist n))
  | _t :: _b :: _m :: _i :: _w :: _r :: _e :: _h :: _c :: _p :: _n ::
      _extra :: _rest => none

private theorem BrouwerBarInductionTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : BrouwerBarInductionUp,
      brouwerBarInductionFromEventFlow (brouwerBarInductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk t b m i w r e h c p n =>
      change
        some
          (BrouwerBarInductionUp.mk
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist t))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist b))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist m))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist i))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist w))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist r))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist e))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist h))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist c))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist p))
            (brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist n))) =
          some (BrouwerBarInductionUp.mk t b m i w r e h c p n)
      rw [BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux t,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux b,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux m,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux i,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux w,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux r,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux e,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux h,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux c,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux p,
        BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux n]

private theorem BrouwerBarInductionTasteGate_single_carrier_alignment_injective_aux
    {x y : BrouwerBarInductionUp} :
    brouwerBarInductionToEventFlow x = brouwerBarInductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerBarInductionFromEventFlow (brouwerBarInductionToEventFlow x) =
        brouwerBarInductionFromEventFlow (brouwerBarInductionToEventFlow y) :=
    congrArg brouwerBarInductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BrouwerBarInductionTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (BrouwerBarInductionTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem BrouwerBarInductionTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : BrouwerBarInductionUp,
      brouwerBarInductionFields x = brouwerBarInductionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk t₁ b₁ m₁ i₁ w₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk t₂ b₂ m₂ i₂ w₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance brouwerBarInductionBHistCarrier :
    BHistCarrier BrouwerBarInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerBarInductionToEventFlow
  fromEventFlow := brouwerBarInductionFromEventFlow

instance brouwerBarInductionChapterTasteGate :
    ChapterTasteGate BrouwerBarInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerBarInductionFromEventFlow (brouwerBarInductionToEventFlow x) = some x
    exact BrouwerBarInductionTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrouwerBarInductionTasteGate_single_carrier_alignment_injective_aux heq)

instance brouwerBarInductionFieldFaithful :
    FieldFaithful BrouwerBarInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerBarInductionFields
  field_faithful := by
    intro x y hfields
    exact BrouwerBarInductionTasteGate_single_carrier_alignment_fields_aux x y hfields

instance brouwerBarInductionNontrivial :
    Nontrivial BrouwerBarInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerBarInductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerBarInductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BrouwerBarInductionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      brouwerBarInductionDecodeBHist (brouwerBarInductionEncodeBHist h) = h) ∧
      (∀ x : BrouwerBarInductionUp,
        brouwerBarInductionFromEventFlow (brouwerBarInductionToEventFlow x) = some x) ∧
      (∀ x y : BrouwerBarInductionUp,
        brouwerBarInductionToEventFlow x = brouwerBarInductionToEventFlow y → x = y) ∧
      brouwerBarInductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BrouwerBarInductionTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact BrouwerBarInductionTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · intro x y heq
        exact BrouwerBarInductionTasteGate_single_carrier_alignment_injective_aux heq
      · rfl

end BEDC.Derived.BrouwerBarInductionUp
