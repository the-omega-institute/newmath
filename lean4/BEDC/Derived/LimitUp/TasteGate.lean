import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitUp : Type where
  | mk (s r d a t c h p n : BHist) : LimitUp
  deriving DecidableEq

def limitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitEncodeBHist h

def limitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitDecodeBHist tail)

private theorem LimitTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitFields : LimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitUp.mk s r d a t c h p n => [s, r, d, a, t, c, h, p, n]

def limitToEventFlow : LimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (limitFields x).map limitEncodeBHist

def limitFromEventFlow : EventFlow → Option LimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _s :: [] => none
  | _s :: _r :: [] => none
  | _s :: _r :: _d :: [] => none
  | _s :: _r :: _d :: _a :: [] => none
  | _s :: _r :: _d :: _a :: _t :: [] => none
  | _s :: _r :: _d :: _a :: _t :: _c :: [] => none
  | _s :: _r :: _d :: _a :: _t :: _c :: _h :: [] => none
  | _s :: _r :: _d :: _a :: _t :: _c :: _h :: _p :: [] => none
  | s :: r :: d :: a :: t :: c :: h :: p :: n :: [] =>
      some
        (LimitUp.mk
          (limitDecodeBHist s)
          (limitDecodeBHist r)
          (limitDecodeBHist d)
          (limitDecodeBHist a)
          (limitDecodeBHist t)
          (limitDecodeBHist c)
          (limitDecodeBHist h)
          (limitDecodeBHist p)
          (limitDecodeBHist n))
  | _s :: _r :: _d :: _a :: _t :: _c :: _h :: _p :: _n :: _extra :: _rest => none

private theorem LimitTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk s r d a t c h p n =>
      change
        some
          (LimitUp.mk
            (limitDecodeBHist (limitEncodeBHist s))
            (limitDecodeBHist (limitEncodeBHist r))
            (limitDecodeBHist (limitEncodeBHist d))
            (limitDecodeBHist (limitEncodeBHist a))
            (limitDecodeBHist (limitEncodeBHist t))
            (limitDecodeBHist (limitEncodeBHist c))
            (limitDecodeBHist (limitEncodeBHist h))
            (limitDecodeBHist (limitEncodeBHist p))
            (limitDecodeBHist (limitEncodeBHist n))) =
          some (LimitUp.mk s r d a t c h p n)
      rw [LimitTasteGate_single_carrier_alignment_decode_aux s,
        LimitTasteGate_single_carrier_alignment_decode_aux r,
        LimitTasteGate_single_carrier_alignment_decode_aux d,
        LimitTasteGate_single_carrier_alignment_decode_aux a,
        LimitTasteGate_single_carrier_alignment_decode_aux t,
        LimitTasteGate_single_carrier_alignment_decode_aux c,
        LimitTasteGate_single_carrier_alignment_decode_aux h,
        LimitTasteGate_single_carrier_alignment_decode_aux p,
        LimitTasteGate_single_carrier_alignment_decode_aux n]

private theorem LimitTasteGate_single_carrier_alignment_injective_aux
    {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitFromEventFlow (limitToEventFlow x) =
        limitFromEventFlow (limitToEventFlow y) :=
    congrArg limitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LimitTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread (LimitTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem LimitTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : LimitUp, limitFields x = limitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk s₁ r₁ d₁ a₁ t₁ c₁ h₁ p₁ n₁ =>
      cases y with
      | mk s₂ r₂ d₂ a₂ t₂ c₂ h₂ p₂ n₂ =>
          cases hfields
          rfl

instance limitBHistCarrier : BHistCarrier LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitToEventFlow
  fromEventFlow := limitFromEventFlow

instance limitChapterTasteGate : ChapterTasteGate LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitFromEventFlow (limitToEventFlow x) = some x
    exact LimitTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LimitTasteGate_single_carrier_alignment_injective_aux heq)

instance limitFieldFaithful : FieldFaithful LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := limitFields
  field_faithful := by
    intro x y hfields
    exact LimitTasteGate_single_carrier_alignment_fields_aux x y hfields

instance limitNontrivial : Nontrivial LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h) ∧
      (∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x) ∧
      (∀ x y : LimitUp, limitToEventFlow x = limitToEventFlow y → x = y) ∧
      limitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LimitTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact LimitTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · intro x y heq
        exact LimitTasteGate_single_carrier_alignment_injective_aux heq
      · rfl

end BEDC.Derived.LimitUp
