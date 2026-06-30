import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BertrandSeriesTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BertrandSeriesTestUp : Type where
  | mk (S Q L D T W R E H C P N : BHist) : BertrandSeriesTestUp
  deriving DecidableEq

def bertrandSeriesTestFields : BertrandSeriesTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BertrandSeriesTestUp.mk S Q L D T W R E H C P N => [S, Q, L, D, T, W, R, E, H, C, P, N]

def bertrandSeriesTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bertrandSeriesTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bertrandSeriesTestEncodeBHist h

def bertrandSeriesTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bertrandSeriesTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bertrandSeriesTestDecodeBHist tail)

private theorem bertrandSeriesTest_decode_encode_bhist :
    ∀ h : BHist, bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bertrandSeriesTestToEventFlow : BertrandSeriesTestUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bertrandSeriesTestFields x).map bertrandSeriesTestEncodeBHist

private def bertrandSeriesTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bertrandSeriesTestEventAtDefault index rest

def bertrandSeriesTestFromEventFlow (ef : EventFlow) : Option BertrandSeriesTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BertrandSeriesTestUp.mk
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 0 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 1 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 2 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 3 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 4 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 5 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 6 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 7 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 8 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 9 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 10 ef))
      (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEventAtDefault 11 ef)))

private theorem bertrandSeriesTest_round_trip :
    ∀ x : BertrandSeriesTestUp,
      bertrandSeriesTestFromEventFlow (bertrandSeriesTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q L D T W R E H C P N =>
      change
        some
          (BertrandSeriesTestUp.mk
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist S))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist Q))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist L))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist D))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist T))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist W))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist R))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist E))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist H))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist C))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist P))
            (bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist N))) =
          some (BertrandSeriesTestUp.mk S Q L D T W R E H C P N)
      rw [bertrandSeriesTest_decode_encode_bhist S, bertrandSeriesTest_decode_encode_bhist Q,
        bertrandSeriesTest_decode_encode_bhist L, bertrandSeriesTest_decode_encode_bhist D,
        bertrandSeriesTest_decode_encode_bhist T, bertrandSeriesTest_decode_encode_bhist W,
        bertrandSeriesTest_decode_encode_bhist R, bertrandSeriesTest_decode_encode_bhist E,
        bertrandSeriesTest_decode_encode_bhist H, bertrandSeriesTest_decode_encode_bhist C,
        bertrandSeriesTest_decode_encode_bhist P, bertrandSeriesTest_decode_encode_bhist N]

private theorem bertrandSeriesTestToEventFlow_injective {x y : BertrandSeriesTestUp} :
    bertrandSeriesTestToEventFlow x = bertrandSeriesTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bertrandSeriesTestFromEventFlow (bertrandSeriesTestToEventFlow x) =
        bertrandSeriesTestFromEventFlow (bertrandSeriesTestToEventFlow y) :=
    congrArg bertrandSeriesTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bertrandSeriesTest_round_trip x).symm
      (Eq.trans hread (bertrandSeriesTest_round_trip y)))

instance bertrandSeriesTestBHistCarrier : BHistCarrier BertrandSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bertrandSeriesTestToEventFlow
  fromEventFlow := bertrandSeriesTestFromEventFlow

instance bertrandSeriesTestChapterTasteGate : ChapterTasteGate BertrandSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bertrandSeriesTestFromEventFlow (bertrandSeriesTestToEventFlow x) = some x
    exact bertrandSeriesTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bertrandSeriesTestToEventFlow_injective heq)

instance bertrandSeriesTestFieldFaithful : FieldFaithful BertrandSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bertrandSeriesTestFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk S₁ Q₁ L₁ D₁ T₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk S₂ Q₂ L₂ D₂ T₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hS rest₁
            injection rest₁ with hQ rest₂
            injection rest₂ with hL rest₃
            injection rest₃ with hD rest₄
            injection rest₄ with hT rest₅
            injection rest₅ with hW rest₆
            injection rest₆ with hR rest₇
            injection rest₇ with hE rest₈
            injection rest₈ with hH rest₉
            injection rest₉ with hC rest₁₀
            injection rest₁₀ with hP rest₁₁
            injection rest₁₁ with hN _
            cases hS
            cases hQ
            cases hL
            cases hD
            cases hT
            cases hW
            cases hR
            cases hE
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance bertrandSeriesTestNontrivial : Nontrivial BertrandSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BertrandSeriesTestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BertrandSeriesTestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty, by
        intro h
        injection h with hS _ _ _ _ _ _ _ _ _ _ _
        cases hS⟩

theorem BertrandSeriesTestTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BertrandSeriesTestUp) ∧
      Nonempty (FieldFaithful BertrandSeriesTestUp) ∧
        Nonempty (Nontrivial BertrandSeriesTestUp) ∧
          (∀ h : BHist,
            bertrandSeriesTestDecodeBHist (bertrandSeriesTestEncodeBHist h) = h) ∧
            (∀ x : BertrandSeriesTestUp,
              bertrandSeriesTestFromEventFlow (bertrandSeriesTestToEventFlow x) = some x) ∧
              (∀ x y : BertrandSeriesTestUp,
                bertrandSeriesTestToEventFlow x = bertrandSeriesTestToEventFlow y → x = y) ∧
                bertrandSeriesTestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨bertrandSeriesTestChapterTasteGate⟩,
      ⟨bertrandSeriesTestFieldFaithful⟩,
      ⟨bertrandSeriesTestNontrivial⟩,
      bertrandSeriesTest_decode_encode_bhist,
      bertrandSeriesTest_round_trip,
      (fun _ _ heq => bertrandSeriesTestToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BertrandSeriesTestUp
