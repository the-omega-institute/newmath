import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySqueezeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySqueezeUp : Type where
  | mk (L M U W D T E H C P N : BHist) : RegularCauchySqueezeUp
  deriving DecidableEq

def regularCauchySqueezeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySqueezeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySqueezeEncodeBHist h

def regularCauchySqueezeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySqueezeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySqueezeDecodeBHist tail)

private theorem RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySqueezeFields : RegularCauchySqueezeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySqueezeUp.mk L M U W D T E H C P N => [L, M, U, W, D, T, E, H, C, P, N]

def regularCauchySqueezeToEventFlow : RegularCauchySqueezeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchySqueezeFields x).map regularCauchySqueezeEncodeBHist

private def regularCauchySqueezeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySqueezeEventAt index rest

def regularCauchySqueezeFromEventFlow (ef : EventFlow) : Option RegularCauchySqueezeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySqueezeUp.mk
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 0 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 1 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 2 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 3 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 4 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 5 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 6 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 7 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 8 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 9 ef))
      (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEventAt 10 ef)))

private theorem RegularCauchySqueezeTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchySqueezeUp) :
    regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L M U W D T E H C P N =>
      change
        some
          (RegularCauchySqueezeUp.mk
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist L))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist M))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist U))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist W))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist D))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist T))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist E))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist H))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist C))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist P))
            (regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist N))) =
          some (RegularCauchySqueezeUp.mk L M U W D T E H C P N)
      rw [RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchySqueezeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySqueezeUp} :
    regularCauchySqueezeToEventFlow x = regularCauchySqueezeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) =
        regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow y) :=
    congrArg regularCauchySqueezeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchySqueezeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySqueezeTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchySqueezeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchySqueezeUp,
      regularCauchySqueezeFields x = regularCauchySqueezeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ M₁ U₁ W₁ D₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ M₂ U₂ W₂ D₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchySqueezeBHistCarrier : BHistCarrier RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySqueezeToEventFlow
  fromEventFlow := regularCauchySqueezeFromEventFlow

instance regularCauchySqueezeChapterTasteGate : ChapterTasteGate RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x
    exact RegularCauchySqueezeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchySqueezeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchySqueezeFieldFaithful : FieldFaithful RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySqueezeFields
  field_faithful := RegularCauchySqueezeTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchySqueezeNontrivial : Nontrivial RegularCauchySqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySqueezeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchySqueezeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchySqueezeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchySqueezeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySqueezeChapterTasteGate

theorem RegularCauchySqueezeTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySqueezeDecodeBHist (regularCauchySqueezeEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySqueezeUp,
        regularCauchySqueezeFromEventFlow (regularCauchySqueezeToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySqueezeUp,
          regularCauchySqueezeToEventFlow x = regularCauchySqueezeToEventFlow y → x = y) ∧
          regularCauchySqueezeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchySqueezeTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchySqueezeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchySqueezeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySqueezeUp
