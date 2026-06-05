import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FubiniFiniteRectangleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FubiniFiniteRectangleUp : Type where
  | mk (R M I P A B D S E H C Q N : BHist) : FubiniFiniteRectangleUp
  deriving DecidableEq

def fubiniFiniteRectangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fubiniFiniteRectangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fubiniFiniteRectangleEncodeBHist h

def fubiniFiniteRectangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fubiniFiniteRectangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fubiniFiniteRectangleDecodeBHist tail)

private theorem FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fubiniFiniteRectangleFields : FubiniFiniteRectangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FubiniFiniteRectangleUp.mk R M I P A B D S E H C Q N =>
      [R, M, I, P, A, B, D, S, E, H, C, Q, N]

def fubiniFiniteRectangleToEventFlow : FubiniFiniteRectangleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (fubiniFiniteRectangleFields x).map fubiniFiniteRectangleEncodeBHist

private def fubiniFiniteRectangleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fubiniFiniteRectangleEventAtDefault index rest

def fubiniFiniteRectangleFromEventFlow
    (ef : EventFlow) : Option FubiniFiniteRectangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FubiniFiniteRectangleUp.mk
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 0 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 1 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 2 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 3 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 4 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 5 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 6 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 7 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 8 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 9 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 10 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 11 ef))
      (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEventAtDefault 12 ef)))

private theorem FubiniFiniteRectangleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FubiniFiniteRectangleUp,
      fubiniFiniteRectangleFromEventFlow (fubiniFiniteRectangleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M I P A B D S E H C Q N =>
      change
        some
          (FubiniFiniteRectangleUp.mk
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist R))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist M))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist I))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist P))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist A))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist B))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist D))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist S))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist E))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist H))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist C))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist Q))
            (fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist N))) =
          some (FubiniFiniteRectangleUp.mk R M I P A B D S E H C Q N)
      rw [FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode R,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode M,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode I,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode P,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode A,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode B,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode D,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode S,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode E,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode H,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode C,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode Q,
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode N]

private theorem FubiniFiniteRectangleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FubiniFiniteRectangleUp} :
    fubiniFiniteRectangleToEventFlow x = fubiniFiniteRectangleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fubiniFiniteRectangleFromEventFlow (fubiniFiniteRectangleToEventFlow x) =
        fubiniFiniteRectangleFromEventFlow (fubiniFiniteRectangleToEventFlow y) :=
    congrArg fubiniFiniteRectangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FubiniFiniteRectangleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FubiniFiniteRectangleTasteGate_single_carrier_alignment_round_trip y)))

private theorem FubiniFiniteRectangleTasteGate_single_carrier_alignment_fields :
    ∀ x y : FubiniFiniteRectangleUp,
      fubiniFiniteRectangleFields x = fubiniFiniteRectangleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ M₁ I₁ P₁ A₁ B₁ D₁ S₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk R₂ M₂ I₂ P₂ A₂ B₂ D₂ S₂ E₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance fubiniFiniteRectangleBHistCarrier :
    BHistCarrier FubiniFiniteRectangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fubiniFiniteRectangleToEventFlow
  fromEventFlow := fubiniFiniteRectangleFromEventFlow

instance fubiniFiniteRectangleChapterTasteGate :
    ChapterTasteGate FubiniFiniteRectangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fubiniFiniteRectangleFromEventFlow (fubiniFiniteRectangleToEventFlow x) =
        some x
    exact FubiniFiniteRectangleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FubiniFiniteRectangleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fubiniFiniteRectangleFieldFaithful :
    FieldFaithful FubiniFiniteRectangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fubiniFiniteRectangleFields
  field_faithful := FubiniFiniteRectangleTasteGate_single_carrier_alignment_fields

instance fubiniFiniteRectangleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FubiniFiniteRectangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FubiniFiniteRectangleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FubiniFiniteRectangleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FubiniFiniteRectangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fubiniFiniteRectangleChapterTasteGate

theorem FubiniFiniteRectangleTasteGate_single_carrier_alignment :
    (∀ h : BHist, fubiniFiniteRectangleDecodeBHist (fubiniFiniteRectangleEncodeBHist h) = h) ∧
      (∀ x : FubiniFiniteRectangleUp,
        fubiniFiniteRectangleFromEventFlow (fubiniFiniteRectangleToEventFlow x) = some x) ∧
        (∀ x y : FubiniFiniteRectangleUp,
          fubiniFiniteRectangleToEventFlow x = fubiniFiniteRectangleToEventFlow y -> x = y) ∧
          fubiniFiniteRectangleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨FubiniFiniteRectangleTasteGate_single_carrier_alignment_decode,
      FubiniFiniteRectangleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FubiniFiniteRectangleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FubiniFiniteRectangleUp
