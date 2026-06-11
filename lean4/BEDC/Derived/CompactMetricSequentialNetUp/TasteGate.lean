import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricSequentialNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricSequentialNetUp : Type where
  | mk (K T L W R E H C P N : BHist) : CompactMetricSequentialNetUp
  deriving DecidableEq

def CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist h

def CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
          (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow :
    CompactMetricSequentialNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricSequentialNetUp.mk K T L W R E H C P N =>
      [[BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist K,
        [BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist N]

private def CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault index rest

def CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CompactMetricSequentialNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactMetricSequentialNetUp.mk
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_eventAtDefault 19 ef)))

private theorem CompactMetricSequentialNetTasteGate_single_carrier_alignment_round_trip
    (x : CompactMetricSequentialNetUp) :
    CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K T L W R E H C P N =>
      change
        some
          (CompactMetricSequentialNetUp.mk
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist K))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist T))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist L))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist W))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist R))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist E))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist H))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist C))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist P))
            (CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
              (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CompactMetricSequentialNetUp.mk K T L W R E H C P N)
      rw [CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist K,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist T,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist L,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist W,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist R,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist E,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist H,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist C,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist P,
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactMetricSequentialNetUp} :
    CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow x =
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow
          (CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow x) =
        CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow
          (CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactMetricSequentialNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactMetricSequentialNetTasteGate_single_carrier_alignment_round_trip y)))

def CompactMetricSequentialNetTasteGate_single_carrier_alignment_fields :
    CompactMetricSequentialNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricSequentialNetUp.mk K T L W R E H C P N => [K, T, L, W, R, E, H, C, P, N]

instance compactMetricSequentialNetBHistCarrier : BHistCarrier CompactMetricSequentialNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow

instance compactMetricSequentialNetChapterTasteGate :
    ChapterTasteGate CompactMetricSequentialNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_fromEventFlow
          (CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompactMetricSequentialNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactMetricSequentialNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactMetricSequentialNetFieldFaithful :
    FieldFaithful CompactMetricSequentialNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CompactMetricSequentialNetTasteGate_single_carrier_alignment_fields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk K₁ T₁ L₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk K₂ T₂ L₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hK rest₁
            injection rest₁ with hT rest₂
            injection rest₂ with hL rest₃
            injection rest₃ with hW rest₄
            injection rest₄ with hR rest₅
            injection rest₅ with hE rest₆
            injection rest₆ with hH rest₇
            injection rest₇ with hC rest₈
            injection rest₈ with hP rest₉
            injection rest₉ with hN _
            cases hK
            cases hT
            cases hL
            cases hW
            cases hR
            cases hE
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance compactMetricSequentialNetNontrivial : Nontrivial CompactMetricSequentialNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactMetricSequentialNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactMetricSequentialNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hK _ _ _ _ _ _ _ _ _
        cases hK⟩

theorem CompactMetricSequentialNetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_decodeBHist
          (CompactMetricSequentialNetTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CompactMetricSequentialNetTasteGate_single_carrier_alignment_fields
          (CompactMetricSequentialNetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact CompactMetricSequentialNetTasteGate_single_carrier_alignment_decode_encode_bhist
  · rfl

end BEDC.Derived.CompactMetricSequentialNetUp
