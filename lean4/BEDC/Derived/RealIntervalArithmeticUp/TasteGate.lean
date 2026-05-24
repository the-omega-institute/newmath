import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalArithmeticUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalArithmeticUp : Type where
  | mk (I J D L T addR mulR E H C P N : BHist) : RealIntervalArithmeticUp
  deriving DecidableEq

def realIntervalArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalArithmeticEncodeBHist h

def realIntervalArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalArithmeticDecodeBHist tail)

private theorem realIntervalArithmetic_decode_encode :
    ∀ h : BHist, realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realIntervalArithmeticFields : RealIntervalArithmeticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalArithmeticUp.mk I J D L T addR mulR E H C P N =>
      [I, J, D, L, T, addR, mulR, E, H, C, P, N]

def realIntervalArithmeticToEventFlow : RealIntervalArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realIntervalArithmeticFields x).map realIntervalArithmeticEncodeBHist

private def RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt index rest

def realIntervalArithmeticFromEventFlow (ef : EventFlow) : Option RealIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalArithmeticUp.mk
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 0 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 1 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 2 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 3 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 4 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 5 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 6 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 7 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 8 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 9 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 10 ef))
      (realIntervalArithmeticDecodeBHist
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem RealIntervalArithmeticTasteGate_single_carrier_alignment_round_trip
    (x : RealIntervalArithmeticUp) :
    realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I J D L T addR mulR E H C P N =>
      change
        some
            (RealIntervalArithmeticUp.mk
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist I))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist J))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist D))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist L))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist T))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist addR))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist mulR))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist E))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist H))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist C))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist P))
              (realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist N))) =
          some (RealIntervalArithmeticUp.mk I J D L T addR mulR E H C P N)
      rw [realIntervalArithmetic_decode_encode I,
        realIntervalArithmetic_decode_encode J,
        realIntervalArithmetic_decode_encode D,
        realIntervalArithmetic_decode_encode L,
        realIntervalArithmetic_decode_encode T,
        realIntervalArithmetic_decode_encode addR,
        realIntervalArithmetic_decode_encode mulR,
        realIntervalArithmetic_decode_encode E,
        realIntervalArithmetic_decode_encode H,
        realIntervalArithmetic_decode_encode C,
        realIntervalArithmetic_decode_encode P,
        realIntervalArithmetic_decode_encode N]

private theorem RealIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealIntervalArithmeticUp} :
    realIntervalArithmeticToEventFlow x = realIntervalArithmeticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) :=
        (RealIntervalArithmeticTasteGate_single_carrier_alignment_round_trip x).symm
      _ = realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow y) :=
        congrArg realIntervalArithmeticFromEventFlow hxy
      _ = some y := RealIntervalArithmeticTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem realIntervalArithmetic_field_faithful :
    ∀ x y : RealIntervalArithmeticUp,
      realIntervalArithmeticFields x = realIntervalArithmeticFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ J₁ D₁ L₁ T₁ addR₁ mulR₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ J₂ D₂ L₂ T₂ addR₂ mulR₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hI tail0
          injection tail0 with hJ tail1
          injection tail1 with hD tail2
          injection tail2 with hL tail3
          injection tail3 with hT tail4
          injection tail4 with haddR tail5
          injection tail5 with hmulR tail6
          injection tail6 with hE tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hI
          subst hJ
          subst hD
          subst hL
          subst hT
          subst haddR
          subst hmulR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realIntervalArithmeticBHistCarrier : BHistCarrier RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalArithmeticToEventFlow
  fromEventFlow := realIntervalArithmeticFromEventFlow

instance realIntervalArithmeticChapterTasteGate :
    ChapterTasteGate RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) = some x
    exact RealIntervalArithmeticTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realIntervalArithmeticFieldFaithful : FieldFaithful RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntervalArithmeticFields
  field_faithful := realIntervalArithmetic_field_faithful

instance realIntervalArithmeticNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealIntervalArithmeticUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealIntervalArithmeticUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalArithmeticChapterTasteGate

theorem RealIntervalArithmeticTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realIntervalArithmeticDecodeBHist (realIntervalArithmeticEncodeBHist h) = h) ∧
      (∀ x : RealIntervalArithmeticUp,
        realIntervalArithmeticFromEventFlow (realIntervalArithmeticToEventFlow x) = some x) ∧
        (∀ x y : RealIntervalArithmeticUp,
          realIntervalArithmeticToEventFlow x = realIntervalArithmeticToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate RealIntervalArithmeticUp) ∧
            (∀ x y : RealIntervalArithmeticUp,
              realIntervalArithmeticFields x = realIntervalArithmeticFields y → x = y) ∧
              (∀ x : RealIntervalArithmeticUp,
                ∃ h : BHist, List.Mem h (realIntervalArithmeticFields x)) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨realIntervalArithmetic_decode_encode,
      RealIntervalArithmeticTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RealIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      ⟨realIntervalArithmeticChapterTasteGate⟩,
      realIntervalArithmetic_field_faithful,
      by
        intro x
        cases x with
        | mk I J D L T addR mulR E H C P N =>
            exact ⟨I, List.Mem.head _⟩⟩

end BEDC.Derived.RealIntervalArithmeticUp.TasteGate
