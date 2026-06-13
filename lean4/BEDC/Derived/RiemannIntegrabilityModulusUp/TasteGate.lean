import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegrabilityModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegrabilityModulusUp : Type where
  | mk (I U L G D R E H C P N : BHist) : RiemannIntegrabilityModulusUp
  deriving DecidableEq

def riemannIntegrabilityModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegrabilityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegrabilityModulusEncodeBHist h

def riemannIntegrabilityModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegrabilityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegrabilityModulusDecodeBHist tail)

theorem RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannIntegrabilityModulusFields :
    RiemannIntegrabilityModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegrabilityModulusUp.mk I U L G D R E H C P N =>
      [I, U, L, G, D, R, E, H, C, P, N]

def riemannIntegrabilityModulusToEventFlow :
    RiemannIntegrabilityModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (riemannIntegrabilityModulusFields x).map
        riemannIntegrabilityModulusEncodeBHist

def riemannIntegrabilityModulusEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      riemannIntegrabilityModulusEventAtDefault index rest

def riemannIntegrabilityModulusFromEventFlow
    (ef : EventFlow) : Option RiemannIntegrabilityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannIntegrabilityModulusUp.mk
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 0 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 1 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 2 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 3 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 4 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 5 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 6 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 7 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 8 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 9 ef))
      (riemannIntegrabilityModulusDecodeBHist
        (riemannIntegrabilityModulusEventAtDefault 10 ef)))

theorem RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_round_trip :
    forall x : RiemannIntegrabilityModulusUp,
      riemannIntegrabilityModulusFromEventFlow
        (riemannIntegrabilityModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I U L G D R E H C P N =>
      change
        some
          (RiemannIntegrabilityModulusUp.mk
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist I))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist U))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist L))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist G))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist D))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist R))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist E))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist H))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist C))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist P))
            (riemannIntegrabilityModulusDecodeBHist
              (riemannIntegrabilityModulusEncodeBHist N))) =
          some (RiemannIntegrabilityModulusUp.mk I U L G D R E H C P N)
      rw [RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode I,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode U,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode L,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode G,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode D,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode R,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode E,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode H,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode C,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode P,
        RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode N]

theorem RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannIntegrabilityModulusUp} :
    riemannIntegrabilityModulusToEventFlow x =
      riemannIntegrabilityModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegrabilityModulusFromEventFlow
          (riemannIntegrabilityModulusToEventFlow x) =
        riemannIntegrabilityModulusFromEventFlow
          (riemannIntegrabilityModulusToEventFlow y) :=
    congrArg riemannIntegrabilityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_round_trip y)))

theorem RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_field_faithful :
    forall x y : RiemannIntegrabilityModulusUp,
      riemannIntegrabilityModulusFields x =
        riemannIntegrabilityModulusFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ U₁ L₁ G₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ U₂ L₂ G₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance riemannIntegrabilityModulusBHistCarrier :
    BHistCarrier RiemannIntegrabilityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegrabilityModulusToEventFlow
  fromEventFlow := riemannIntegrabilityModulusFromEventFlow

instance riemannIntegrabilityModulusChapterTasteGate :
    ChapterTasteGate RiemannIntegrabilityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id
      (RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance riemannIntegrabilityModulusFieldFaithful :
    FieldFaithful RiemannIntegrabilityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannIntegrabilityModulusFields
  field_faithful :=
    RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_field_faithful

def riemannIntegrabilityModulusTasteGate :
    ChapterTasteGate RiemannIntegrabilityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegrabilityModulusChapterTasteGate

theorem RiemannIntegrabilityModulusTasteGate_single_carrier_alignment :
    (riemannIntegrabilityModulusEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        riemannIntegrabilityModulusDecodeBHist
          (riemannIntegrabilityModulusEncodeBHist h) = h) ∧
      (∀ x : RiemannIntegrabilityModulusUp,
        riemannIntegrabilityModulusFromEventFlow
          (riemannIntegrabilityModulusToEventFlow x) = some x) ∧
      (∀ x y : RiemannIntegrabilityModulusUp,
        riemannIntegrabilityModulusFields x =
          riemannIntegrabilityModulusFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨rfl,
      RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_decode_encode,
      RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_round_trip,
      RiemannIntegrabilityModulusTasteGate_single_carrier_alignment_field_faithful⟩

end BEDC.Derived.RiemannIntegrabilityModulusUp.TasteGate
