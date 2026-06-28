import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanTheoremBarModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanTheoremBarModulusUp : Type where
  | mk (F B W L R U H C P N : BHist) : FanTheoremBarModulusUp
  deriving DecidableEq

def fanTheoremBarModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanTheoremBarModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanTheoremBarModulusEncodeBHist h

def fanTheoremBarModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanTheoremBarModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanTheoremBarModulusDecodeBHist tail)

private theorem FanTheoremBarModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def fanTheoremBarModulusFields : FanTheoremBarModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanTheoremBarModulusUp.mk F B W L R U H C P N => [F, B, W, L, R, U, H, C, P, N]

def fanTheoremBarModulusToEventFlow : FanTheoremBarModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b0, BMark.b1, BMark.b0] ::
        (fanTheoremBarModulusFields x).map fanTheoremBarModulusEncodeBHist

private def fanTheoremBarModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fanTheoremBarModulusEventAt index rest

def fanTheoremBarModulusFromEventFlow (ef : EventFlow) : Option FanTheoremBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | _header :: rows =>
      some
        (FanTheoremBarModulusUp.mk
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 0 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 1 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 2 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 3 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 4 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 5 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 6 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 7 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 8 rows))
          (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEventAt 9 rows)))
  | [] => none

private theorem FanTheoremBarModulusTasteGate_single_carrier_alignment_round_trip
    (x : FanTheoremBarModulusUp) :
    fanTheoremBarModulusFromEventFlow (fanTheoremBarModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F B W L R U H C P N =>
      change
        some
          (FanTheoremBarModulusUp.mk
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist F))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist B))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist W))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist L))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist R))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist U))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist H))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist C))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist P))
            (fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist N))) =
          some (FanTheoremBarModulusUp.mk F B W L R U H C P N)
      rw [FanTheoremBarModulusTasteGate_single_carrier_alignment_decode F,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode B,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode W,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode L,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode R,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode U,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode H,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode C,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode P,
        FanTheoremBarModulusTasteGate_single_carrier_alignment_decode N]

private theorem FanTheoremBarModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FanTheoremBarModulusUp} :
    fanTheoremBarModulusToEventFlow x = fanTheoremBarModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanTheoremBarModulusFromEventFlow (fanTheoremBarModulusToEventFlow x) =
        fanTheoremBarModulusFromEventFlow (fanTheoremBarModulusToEventFlow y) :=
    congrArg fanTheoremBarModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FanTheoremBarModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FanTheoremBarModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem FanTheoremBarModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : FanTheoremBarModulusUp,
      fanTheoremBarModulusFields x = fanTheoremBarModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ B₁ W₁ L₁ R₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ B₂ W₂ L₂ R₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance fanTheoremBarModulusBHistCarrier : BHistCarrier FanTheoremBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanTheoremBarModulusToEventFlow
  fromEventFlow := fanTheoremBarModulusFromEventFlow

instance fanTheoremBarModulusChapterTasteGate : ChapterTasteGate FanTheoremBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanTheoremBarModulusFromEventFlow (fanTheoremBarModulusToEventFlow x) = some x
    exact FanTheoremBarModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FanTheoremBarModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fanTheoremBarModulusFieldFaithful : FieldFaithful FanTheoremBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fanTheoremBarModulusFields
  field_faithful := FanTheoremBarModulusTasteGate_single_carrier_alignment_fields

instance fanTheoremBarModulusNontrivial : Nontrivial FanTheoremBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FanTheoremBarModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FanTheoremBarModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FanTheoremBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanTheoremBarModulusChapterTasteGate

theorem FanTheoremBarModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, fanTheoremBarModulusDecodeBHist (fanTheoremBarModulusEncodeBHist h) = h) ∧
      (∀ x : FanTheoremBarModulusUp,
        fanTheoremBarModulusFromEventFlow (fanTheoremBarModulusToEventFlow x) = some x) ∧
        (∀ x y : FanTheoremBarModulusUp,
          fanTheoremBarModulusToEventFlow x = fanTheoremBarModulusToEventFlow y → x = y) ∧
          fanTheoremBarModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FanTheoremBarModulusTasteGate_single_carrier_alignment_decode,
      FanTheoremBarModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FanTheoremBarModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FanTheoremBarModulusUp
