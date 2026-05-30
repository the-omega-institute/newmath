import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCoveringNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCoveringNumberUp : Type where
  | mk (X eps P C D B H R S N : BHist) : MetricCoveringNumberUp
  deriving DecidableEq

def metricCoveringNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCoveringNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCoveringNumberEncodeBHist h

def metricCoveringNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCoveringNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCoveringNumberDecodeBHist tail)

private theorem metricCoveringNumber_decode_encode_bhist :
    ∀ h : BHist, metricCoveringNumberDecodeBHist (metricCoveringNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem metricCoveringNumber_mk_congr
    {X X' eps eps' P P' C C' D D' B B' H H' R R' S S' N N' : BHist}
    (hX : X' = X)
    (heps : eps' = eps)
    (hP : P' = P)
    (hC : C' = C)
    (hD : D' = D)
    (hB : B' = B)
    (hH : H' = H)
    (hR : R' = R)
    (hS : S' = S)
    (hN : N' = N) :
    MetricCoveringNumberUp.mk X' eps' P' C' D' B' H' R' S' N' =
      MetricCoveringNumberUp.mk X eps P C D B H R S N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases heps
  cases hP
  cases hC
  cases hD
  cases hB
  cases hH
  cases hR
  cases hS
  cases hN
  rfl

def metricCoveringNumberFields : MetricCoveringNumberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCoveringNumberUp.mk X eps P C D B H R S N => [X, eps, P, C, D, B, H, R, S, N]

def metricCoveringNumberToEventFlow : MetricCoveringNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCoveringNumberUp.mk X eps P C D B H R S N =>
      [metricCoveringNumberEncodeBHist X,
        metricCoveringNumberEncodeBHist eps,
        metricCoveringNumberEncodeBHist P,
        metricCoveringNumberEncodeBHist C,
        metricCoveringNumberEncodeBHist D,
        metricCoveringNumberEncodeBHist B,
        metricCoveringNumberEncodeBHist H,
        metricCoveringNumberEncodeBHist R,
        metricCoveringNumberEncodeBHist S,
        metricCoveringNumberEncodeBHist N]

private def metricCoveringNumberEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCoveringNumberEventAtDefault index rest

def metricCoveringNumberFromEventFlow (ef : EventFlow) : Option MetricCoveringNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCoveringNumberUp.mk
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 0 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 1 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 2 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 3 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 4 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 5 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 6 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 7 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 8 ef))
      (metricCoveringNumberDecodeBHist (metricCoveringNumberEventAtDefault 9 ef)))

private theorem metricCoveringNumber_round_trip :
    ∀ x : MetricCoveringNumberUp,
      metricCoveringNumberFromEventFlow (metricCoveringNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X eps P C D B H R S N =>
      exact
        congrArg some
          (metricCoveringNumber_mk_congr
            (metricCoveringNumber_decode_encode_bhist X)
            (metricCoveringNumber_decode_encode_bhist eps)
            (metricCoveringNumber_decode_encode_bhist P)
            (metricCoveringNumber_decode_encode_bhist C)
            (metricCoveringNumber_decode_encode_bhist D)
            (metricCoveringNumber_decode_encode_bhist B)
            (metricCoveringNumber_decode_encode_bhist H)
            (metricCoveringNumber_decode_encode_bhist R)
            (metricCoveringNumber_decode_encode_bhist S)
            (metricCoveringNumber_decode_encode_bhist N))

private theorem metricCoveringNumberToEventFlow_injective {x y : MetricCoveringNumberUp} :
    metricCoveringNumberToEventFlow x = metricCoveringNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCoveringNumberFromEventFlow (metricCoveringNumberToEventFlow x) =
        metricCoveringNumberFromEventFlow (metricCoveringNumberToEventFlow y) :=
    congrArg metricCoveringNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricCoveringNumber_round_trip x).symm
      (Eq.trans hread (metricCoveringNumber_round_trip y)))

private theorem metricCoveringNumber_fields_faithful :
    ∀ x y : MetricCoveringNumberUp,
      metricCoveringNumberFields x = metricCoveringNumberFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ eps₁ P₁ C₁ D₁ B₁ H₁ R₁ S₁ N₁ =>
      cases y with
      | mk X₂ eps₂ P₂ C₂ D₂ B₂ H₂ R₂ S₂ N₂ =>
          cases hfields
          rfl

instance metricCoveringNumberBHistCarrier : BHistCarrier MetricCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCoveringNumberToEventFlow
  fromEventFlow := metricCoveringNumberFromEventFlow

instance metricCoveringNumberChapterTasteGate : ChapterTasteGate MetricCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCoveringNumberFromEventFlow (metricCoveringNumberToEventFlow x) = some x
    exact metricCoveringNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCoveringNumberToEventFlow_injective heq)

instance metricCoveringNumberFieldFaithful : FieldFaithful MetricCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCoveringNumberFields
  field_faithful := metricCoveringNumber_fields_faithful

instance metricCoveringNumberNontrivial : Nontrivial MetricCoveringNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCoveringNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCoveringNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCoveringNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCoveringNumberChapterTasteGate

theorem MetricCoveringNumberTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCoveringNumberUp) ∧
      Nonempty (FieldFaithful MetricCoveringNumberUp) ∧
        Nonempty (Nontrivial MetricCoveringNumberUp) ∧
          (∀ h : BHist, metricCoveringNumberDecodeBHist (metricCoveringNumberEncodeBHist h) = h) ∧
            (∀ x : MetricCoveringNumberUp,
              metricCoveringNumberFromEventFlow (metricCoveringNumberToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro metricCoveringNumberChapterTasteGate,
      Nonempty.intro metricCoveringNumberFieldFaithful,
      Nonempty.intro metricCoveringNumberNontrivial,
      metricCoveringNumber_decode_encode_bhist,
      metricCoveringNumber_round_trip⟩

end BEDC.Derived.MetricCoveringNumberUp
