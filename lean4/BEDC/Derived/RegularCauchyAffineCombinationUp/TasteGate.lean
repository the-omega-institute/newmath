import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAffineCombinationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAffineCombinationUp : Type where
  | mk (q x y wx wy dq dbarq sx sy sum e r z h c p n : BHist) :
      RegularCauchyAffineCombinationUp
  deriving DecidableEq

def regularCauchyAffineCombinationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAffineCombinationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAffineCombinationEncodeBHist h

def regularCauchyAffineCombinationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAffineCombinationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAffineCombinationDecodeBHist tail)

private theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyAffineCombinationFields :
    RegularCauchyAffineCombinationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyAffineCombinationUp.mk q x y wx wy dq dbarq sx sy sum e r z h c p n =>
      [q, x, y, wx, wy, dq, dbarq, sx, sy, sum, e, r, z, h, c, p, n]

def regularCauchyAffineCombinationToEventFlow :
    RegularCauchyAffineCombinationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyAffineCombinationFields x).map regularCauchyAffineCombinationEncodeBHist

def regularCauchyAffineCombinationFromEventFlow :
    EventFlow → Option RegularCauchyAffineCombinationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _q :: [] => none
  | _q :: _x :: [] => none
  | _q :: _x :: _y :: [] => none
  | _q :: _x :: _y :: _wx :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: _z :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: _z :: _h :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: _z :: _h :: _c :: [] => none
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: _z :: _h :: _c :: _p :: [] => none
  | q :: x :: y :: wx :: wy :: dq :: dbarq :: sx :: sy :: sum :: e ::
      r :: z :: h :: c :: p :: n :: [] =>
      some
        (RegularCauchyAffineCombinationUp.mk
          (regularCauchyAffineCombinationDecodeBHist q)
          (regularCauchyAffineCombinationDecodeBHist x)
          (regularCauchyAffineCombinationDecodeBHist y)
          (regularCauchyAffineCombinationDecodeBHist wx)
          (regularCauchyAffineCombinationDecodeBHist wy)
          (regularCauchyAffineCombinationDecodeBHist dq)
          (regularCauchyAffineCombinationDecodeBHist dbarq)
          (regularCauchyAffineCombinationDecodeBHist sx)
          (regularCauchyAffineCombinationDecodeBHist sy)
          (regularCauchyAffineCombinationDecodeBHist sum)
          (regularCauchyAffineCombinationDecodeBHist e)
          (regularCauchyAffineCombinationDecodeBHist r)
          (regularCauchyAffineCombinationDecodeBHist z)
          (regularCauchyAffineCombinationDecodeBHist h)
          (regularCauchyAffineCombinationDecodeBHist c)
          (regularCauchyAffineCombinationDecodeBHist p)
          (regularCauchyAffineCombinationDecodeBHist n))
  | _q :: _x :: _y :: _wx :: _wy :: _dq :: _dbarq :: _sx :: _sy :: _sum ::
      _e :: _r :: _z :: _h :: _c :: _p :: _n :: _extra :: _rest => none

private theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : RegularCauchyAffineCombinationUp,
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q x y wx wy dq dbarq sx sy sum e r z h c p n =>
      change
        some
          (RegularCauchyAffineCombinationUp.mk
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist q))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist x))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist y))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist wx))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist wy))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist dq))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist dbarq))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist sx))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist sy))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist sum))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist e))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist r))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist z))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist h))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist c))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist p))
            (regularCauchyAffineCombinationDecodeBHist
              (regularCauchyAffineCombinationEncodeBHist n))) =
          some (RegularCauchyAffineCombinationUp.mk q x y wx wy dq dbarq sx sy sum e r z h c p n)
      rw [RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux q,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux x,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux y,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux wx,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux wy,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux dq,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux dbarq,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux sx,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux sy,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux sum,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux e,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux r,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux z,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux h,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux c,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux p,
        RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux n]

private theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_injective_aux
    {x y : RegularCauchyAffineCombinationUp} :
    regularCauchyAffineCombinationToEventFlow x =
      regularCauchyAffineCombinationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow y) :=
    congrArg regularCauchyAffineCombinationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip_aux x).symm
      (Eq.trans hread
        (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip_aux y)))

private theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : RegularCauchyAffineCombinationUp,
      regularCauchyAffineCombinationFields x = regularCauchyAffineCombinationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q₁ x₁ y₁ wx₁ wy₁ dq₁ dbarq₁ sx₁ sy₁ sum₁ e₁ r₁ z₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk q₂ x₂ y₂ wx₂ wy₂ dq₂ dbarq₂ sx₂ sy₂ sum₂ e₂ r₂ z₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance regularCauchyAffineCombinationBHistCarrier :
    BHistCarrier RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAffineCombinationToEventFlow
  fromEventFlow := regularCauchyAffineCombinationFromEventFlow

instance regularCauchyAffineCombinationChapterTasteGate :
    ChapterTasteGate RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyAffineCombinationFromEventFlow
          (regularCauchyAffineCombinationToEventFlow x) =
        some x
    exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip_aux x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_injective_aux heq)

instance regularCauchyAffineCombinationFieldFaithful :
    FieldFaithful RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyAffineCombinationFields
  field_faithful := by
    intro x y hfields
    exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_fields_aux x y hfields

instance regularCauchyAffineCombinationNontrivial :
    Nontrivial RegularCauchyAffineCombinationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyAffineCombinationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyAffineCombinationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyAffineCombinationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyAffineCombinationDecodeBHist
        (regularCauchyAffineCombinationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyAffineCombinationUp,
        regularCauchyAffineCombinationFromEventFlow
            (regularCauchyAffineCombinationToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyAffineCombinationUp,
        regularCauchyAffineCombinationToEventFlow x =
          regularCauchyAffineCombinationToEventFlow y → x = y) ∧
      regularCauchyAffineCombinationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_round_trip_aux
    · constructor
      · intro x y heq
        exact RegularCauchyAffineCombinationTasteGate_single_carrier_alignment_injective_aux heq
      · rfl

end BEDC.Derived.RegularCauchyAffineCombinationUp
