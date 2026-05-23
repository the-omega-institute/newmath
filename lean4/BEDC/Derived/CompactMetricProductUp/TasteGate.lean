import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricProductUp : Type where
  | mk (X Y M P T L H C Q N : BHist) : CompactMetricProductUp
  deriving DecidableEq

def compactMetricProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricProductEncodeBHist h

def compactMetricProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricProductDecodeBHist tail)

private theorem CompactMetricProductTasteGate_decode_encode :
    ∀ h : BHist,
      compactMetricProductDecodeBHist (compactMetricProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricProductToEventFlow : CompactMetricProductUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricProductUp.mk X Y M P T L H C Q N =>
      [compactMetricProductEncodeBHist X,
        compactMetricProductEncodeBHist Y,
        compactMetricProductEncodeBHist M,
        compactMetricProductEncodeBHist P,
        compactMetricProductEncodeBHist T,
        compactMetricProductEncodeBHist L,
        compactMetricProductEncodeBHist H,
        compactMetricProductEncodeBHist C,
        compactMetricProductEncodeBHist Q,
        compactMetricProductEncodeBHist N]

private def compactMetricProductEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactMetricProductEventAtDefault index rest

def compactMetricProductFromEventFlow : EventFlow → Option CompactMetricProductUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompactMetricProductUp.mk
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 0 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 1 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 2 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 3 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 4 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 5 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 6 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 7 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 8 ef))
          (compactMetricProductDecodeBHist (compactMetricProductEventAtDefault 9 ef)))

private theorem CompactMetricProductTasteGate_round_trip
    (x : CompactMetricProductUp) :
    compactMetricProductFromEventFlow (compactMetricProductToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y M P T L H C Q N =>
      change
        some
          (CompactMetricProductUp.mk
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist X))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist Y))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist M))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist P))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist T))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist L))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist H))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist C))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist Q))
            (compactMetricProductDecodeBHist (compactMetricProductEncodeBHist N))) =
          some (CompactMetricProductUp.mk X Y M P T L H C Q N)
      rw [CompactMetricProductTasteGate_decode_encode X,
        CompactMetricProductTasteGate_decode_encode Y,
        CompactMetricProductTasteGate_decode_encode M,
        CompactMetricProductTasteGate_decode_encode P,
        CompactMetricProductTasteGate_decode_encode T,
        CompactMetricProductTasteGate_decode_encode L,
        CompactMetricProductTasteGate_decode_encode H,
        CompactMetricProductTasteGate_decode_encode C,
        CompactMetricProductTasteGate_decode_encode Q,
        CompactMetricProductTasteGate_decode_encode N]

private theorem CompactMetricProductTasteGate_toEventFlow_injective
    {x y : CompactMetricProductUp} :
    compactMetricProductToEventFlow x = compactMetricProductToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricProductFromEventFlow (compactMetricProductToEventFlow x) =
        compactMetricProductFromEventFlow (compactMetricProductToEventFlow y) :=
    congrArg compactMetricProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactMetricProductTasteGate_round_trip x).symm
      (Eq.trans hread (CompactMetricProductTasteGate_round_trip y)))

instance compactMetricProductBHistCarrier : BHistCarrier CompactMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricProductToEventFlow
  fromEventFlow := compactMetricProductFromEventFlow

instance compactMetricProductChapterTasteGate :
    ChapterTasteGate CompactMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactMetricProductFromEventFlow (compactMetricProductToEventFlow x) = some x
    exact CompactMetricProductTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactMetricProductTasteGate_toEventFlow_injective heq)

instance compactMetricProductFieldFaithful : FieldFaithful CompactMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun
    | CompactMetricProductUp.mk X Y M P T L H C Q N => [X, Y, M, P, T, L, H, C, Q, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk X1 Y1 M1 P1 T1 L1 H1 C1 Q1 N1 =>
        cases y with
        | mk X2 Y2 M2 P2 T2 L2 H2 C2 Q2 N2 =>
            cases hfields
            rfl

instance compactMetricProductNontrivial : Nontrivial CompactMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactMetricProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactMetricProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactMetricProductTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactMetricProductDecodeBHist (compactMetricProductEncodeBHist h) = h) ∧
      (∀ x : CompactMetricProductUp,
        compactMetricProductFromEventFlow (compactMetricProductToEventFlow x) = some x) ∧
        (∀ x y : CompactMetricProductUp,
          compactMetricProductToEventFlow x = compactMetricProductToEventFlow y → x = y) ∧
          compactMetricProductEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompactMetricProductTasteGate_decode_encode,
      CompactMetricProductTasteGate_round_trip,
      (fun _ _ heq => CompactMetricProductTasteGate_toEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem CompactMetricProductTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactMetricProductUp) ∧
      Nonempty (FieldFaithful CompactMetricProductUp) ∧
      Nonempty (Nontrivial CompactMetricProductUp) ∧
      (∀ h : BHist, compactMetricProductDecodeBHist (compactMetricProductEncodeBHist h) = h) ∧
      (∀ x : CompactMetricProductUp,
        compactMetricProductFromEventFlow (compactMetricProductToEventFlow x) = some x) ∧
      (∀ x y : CompactMetricProductUp,
        compactMetricProductToEventFlow x = compactMetricProductToEventFlow y → x = y) ∧
      compactMetricProductEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro compactMetricProductChapterTasteGate,
      Nonempty.intro compactMetricProductFieldFaithful,
      Nonempty.intro compactMetricProductNontrivial,
      CompactMetricProductTasteGate_decode_encode,
      CompactMetricProductTasteGate_round_trip,
      (fun _ _ heq => CompactMetricProductTasteGate_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.CompactMetricProductUp
