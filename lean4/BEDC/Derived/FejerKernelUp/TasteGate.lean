import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FejerKernelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FejerKernelUp : Type where
  | mk (F S A I U P T C Q N : BHist) : FejerKernelUp
  deriving DecidableEq

def fejerKernelEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fejerKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fejerKernelEncodeBHist h

def fejerKernelDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fejerKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fejerKernelDecodeBHist tail)

private theorem FejerKernelTasteGate_single_carrier_alignment_decode :
    forall h : BHist, fejerKernelDecodeBHist (fejerKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fejerKernelToEventFlow : FejerKernelUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FejerKernelUp.mk F S A I U P T C Q N =>
      [fejerKernelEncodeBHist F,
        fejerKernelEncodeBHist S,
        fejerKernelEncodeBHist A,
        fejerKernelEncodeBHist I,
        fejerKernelEncodeBHist U,
        fejerKernelEncodeBHist P,
        fejerKernelEncodeBHist T,
        fejerKernelEncodeBHist C,
        fejerKernelEncodeBHist Q,
        fejerKernelEncodeBHist N]

private def fejerKernelEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fejerKernelEventAtDefault index rest

def fejerKernelFromEventFlow (ef : EventFlow) : Option FejerKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FejerKernelUp.mk
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 0 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 1 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 2 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 3 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 4 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 5 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 6 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 7 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 8 ef))
      (fejerKernelDecodeBHist (fejerKernelEventAtDefault 9 ef)))

private theorem FejerKernelTasteGate_single_carrier_alignment_round_trip :
    forall x : FejerKernelUp,
      fejerKernelFromEventFlow (fejerKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S A I U P T C Q N =>
      change
        some
          (FejerKernelUp.mk
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist F))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist S))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist A))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist I))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist U))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist P))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist T))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist C))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist Q))
            (fejerKernelDecodeBHist (fejerKernelEncodeBHist N))) =
          some (FejerKernelUp.mk F S A I U P T C Q N)
      rw [FejerKernelTasteGate_single_carrier_alignment_decode F,
        FejerKernelTasteGate_single_carrier_alignment_decode S,
        FejerKernelTasteGate_single_carrier_alignment_decode A,
        FejerKernelTasteGate_single_carrier_alignment_decode I,
        FejerKernelTasteGate_single_carrier_alignment_decode U,
        FejerKernelTasteGate_single_carrier_alignment_decode P,
        FejerKernelTasteGate_single_carrier_alignment_decode T,
        FejerKernelTasteGate_single_carrier_alignment_decode C,
        FejerKernelTasteGate_single_carrier_alignment_decode Q,
        FejerKernelTasteGate_single_carrier_alignment_decode N]

private theorem FejerKernelTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FejerKernelUp} :
    fejerKernelToEventFlow x = fejerKernelToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fejerKernelFromEventFlow (fejerKernelToEventFlow x) =
        fejerKernelFromEventFlow (fejerKernelToEventFlow y) :=
    congrArg fejerKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FejerKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FejerKernelTasteGate_single_carrier_alignment_round_trip y)))

private def fejerKernelFields : FejerKernelUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FejerKernelUp.mk F S A I U P T C Q N => [F, S, A, I, U, P, T, C, Q, N]

private theorem FejerKernelTasteGate_single_carrier_alignment_fields :
    forall x y : FejerKernelUp, fejerKernelFields x = fejerKernelFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 S1 A1 I1 U1 P1 T1 C1 Q1 N1 =>
      cases y with
      | mk F2 S2 A2 I2 U2 P2 T2 C2 Q2 N2 =>
          cases hfields
          rfl

instance fejerKernelBHistCarrier : BHistCarrier FejerKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fejerKernelToEventFlow
  fromEventFlow := fejerKernelFromEventFlow

instance fejerKernelChapterTasteGate : ChapterTasteGate FejerKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fejerKernelFromEventFlow (fejerKernelToEventFlow x) = some x
    exact FejerKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FejerKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance fejerKernelFieldFaithful : FieldFaithful FejerKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fejerKernelFields
  field_faithful := FejerKernelTasteGate_single_carrier_alignment_fields

instance fejerKernelNontrivial : Nontrivial FejerKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FejerKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FejerKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FejerKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fejerKernelChapterTasteGate

theorem FejerKernelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FejerKernelUp) ∧
      Nonempty (FieldFaithful FejerKernelUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FejerKernelUp) ∧
          (∀ h : BHist, fejerKernelDecodeBHist (fejerKernelEncodeBHist h) = h) ∧
            (∀ x : FejerKernelUp,
              fejerKernelFromEventFlow (fejerKernelToEventFlow x) = some x) ∧
              (∀ x y : FejerKernelUp,
                fejerKernelToEventFlow x = fejerKernelToEventFlow y -> x = y) ∧
                (BHistCarrier.toEventFlow
                    (FejerKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
                  [fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty,
                    fejerKernelEncodeBHist BHist.Empty]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨fejerKernelChapterTasteGate⟩,
      ⟨fejerKernelFieldFaithful⟩,
      ⟨fejerKernelNontrivial⟩,
      FejerKernelTasteGate_single_carrier_alignment_decode,
      FejerKernelTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FejerKernelTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FejerKernelUp
