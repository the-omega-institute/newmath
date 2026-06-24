import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannSumCauchyNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannSumCauchyNetUp : Type where
  | mk (D W R M S E Q H C P N : BHist) : RiemannSumCauchyNetUp
  deriving DecidableEq

def riemannSumCauchyNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannSumCauchyNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannSumCauchyNetEncodeBHist h

def riemannSumCauchyNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannSumCauchyNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannSumCauchyNetDecodeBHist tail)

private theorem RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannSumCauchyNetFields : RiemannSumCauchyNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannSumCauchyNetUp.mk D W R M S E Q H C P N => [D, W, R, M, S, E, Q, H, C, P, N]

def riemannSumCauchyNetToEventFlow : RiemannSumCauchyNetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (riemannSumCauchyNetFields x).map riemannSumCauchyNetEncodeBHist

private def riemannSumCauchyNetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannSumCauchyNetEventAt index rest

def riemannSumCauchyNetFromEventFlow (ef : EventFlow) :
    Option RiemannSumCauchyNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannSumCauchyNetUp.mk
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 0 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 1 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 2 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 3 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 4 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 5 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 6 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 7 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 8 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 9 ef))
      (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEventAt 10 ef)))

private theorem RiemannSumCauchyNetTasteGate_single_carrier_alignment_round_trip
    (x : RiemannSumCauchyNetUp) :
    riemannSumCauchyNetFromEventFlow (riemannSumCauchyNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W R M S E Q H C P N =>
      change
        some
          (RiemannSumCauchyNetUp.mk
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist D))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist W))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist R))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist M))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist S))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist E))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist Q))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist H))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist C))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist P))
            (riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist N))) =
          some (RiemannSumCauchyNetUp.mk D W R M S E Q H C P N)
      rw [RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode D,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode W,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode R,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode M,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode S,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode E,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode Q,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode H,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode C,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode P,
        RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode N]

private theorem RiemannSumCauchyNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannSumCauchyNetUp} :
    riemannSumCauchyNetToEventFlow x = riemannSumCauchyNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannSumCauchyNetFromEventFlow (riemannSumCauchyNetToEventFlow x) =
        riemannSumCauchyNetFromEventFlow (riemannSumCauchyNetToEventFlow y) :=
    congrArg riemannSumCauchyNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannSumCauchyNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RiemannSumCauchyNetTasteGate_single_carrier_alignment_round_trip y)))

private theorem RiemannSumCauchyNetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RiemannSumCauchyNetUp, riemannSumCauchyNetFields x = riemannSumCauchyNetFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ R₁ M₁ S₁ E₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ R₂ M₂ S₂ E₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance riemannSumCauchyNetBHistCarrier : BHistCarrier RiemannSumCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannSumCauchyNetToEventFlow
  fromEventFlow := riemannSumCauchyNetFromEventFlow

instance riemannSumCauchyNetChapterTasteGate :
    ChapterTasteGate RiemannSumCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change riemannSumCauchyNetFromEventFlow (riemannSumCauchyNetToEventFlow x) = some x
    exact RiemannSumCauchyNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannSumCauchyNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance riemannSumCauchyNetFieldFaithful : FieldFaithful RiemannSumCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannSumCauchyNetFields
  field_faithful := RiemannSumCauchyNetTasteGate_single_carrier_alignment_fields_faithful

instance riemannSumCauchyNetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RiemannSumCauchyNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannSumCauchyNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RiemannSumCauchyNetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RiemannSumCauchyNetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RiemannSumCauchyNetUp) ∧
      Nonempty (FieldFaithful RiemannSumCauchyNetUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RiemannSumCauchyNetUp) ∧
      (∀ h : BHist, riemannSumCauchyNetDecodeBHist (riemannSumCauchyNetEncodeBHist h) = h) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨riemannSumCauchyNetChapterTasteGate⟩, ⟨riemannSumCauchyNetFieldFaithful⟩,
      ⟨riemannSumCauchyNetNontrivial⟩,
      RiemannSumCauchyNetTasteGate_single_carrier_alignment_decode_encode⟩

end BEDC.Derived.RiemannSumCauchyNetUp
