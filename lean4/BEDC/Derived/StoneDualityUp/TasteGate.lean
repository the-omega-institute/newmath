import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StoneDualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StoneDualityUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (zero one meet join compl distributive source pkgRow : BHist) ->
        StoneDualityUp
  deriving DecidableEq

def StoneDualityTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: StoneDualityTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: StoneDualityTasteGate_single_carrier_alignment_encodeBHist h

def StoneDualityTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (StoneDualityTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (StoneDualityTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem StoneDualityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      StoneDualityTasteGate_single_carrier_alignment_decodeBHist
        (StoneDualityTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def StoneDualityTasteGate_single_carrier_alignment_fields :
    StoneDualityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StoneDualityUp.mk zero one meet join compl distributive source pkgRow =>
      [zero, one, meet, join, compl, distributive, source, pkgRow]

def StoneDualityTasteGate_single_carrier_alignment_toEventFlow :
    StoneDualityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (StoneDualityTasteGate_single_carrier_alignment_fields x).map
        StoneDualityTasteGate_single_carrier_alignment_encodeBHist

def StoneDualityTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option StoneDualityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [zero, one, meet, join, compl, distributive, source, pkgRow] =>
      some
        (StoneDualityUp.mk
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist zero)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist one)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist meet)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist join)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist compl)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist distributive)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist source)
          (StoneDualityTasteGate_single_carrier_alignment_decodeBHist pkgRow))
  | _ => none

private theorem StoneDualityTasteGate_single_carrier_alignment_round_trip
    (x : StoneDualityUp) :
    StoneDualityTasteGate_single_carrier_alignment_fromEventFlow
      (StoneDualityTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk zero one meet join compl distributive source pkgRow =>
      change
        some
          (StoneDualityUp.mk
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist zero))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist one))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist meet))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist join))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist compl))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist distributive))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist source))
            (StoneDualityTasteGate_single_carrier_alignment_decodeBHist
              (StoneDualityTasteGate_single_carrier_alignment_encodeBHist pkgRow))) =
          some (StoneDualityUp.mk zero one meet join compl distributive source pkgRow)
      rw [StoneDualityTasteGate_single_carrier_alignment_decode_encode zero,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode one,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode meet,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode join,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode compl,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode distributive,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode source,
        StoneDualityTasteGate_single_carrier_alignment_decode_encode pkgRow]

private theorem StoneDualityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : StoneDualityUp} :
    StoneDualityTasteGate_single_carrier_alignment_toEventFlow x =
        StoneDualityTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      StoneDualityTasteGate_single_carrier_alignment_fromEventFlow
          (StoneDualityTasteGate_single_carrier_alignment_toEventFlow x) =
        StoneDualityTasteGate_single_carrier_alignment_fromEventFlow
          (StoneDualityTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg StoneDualityTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StoneDualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StoneDualityTasteGate_single_carrier_alignment_round_trip y)))

private theorem StoneDualityTasteGate_single_carrier_alignment_fields_faithful
    (x y : StoneDualityUp) :
    StoneDualityTasteGate_single_carrier_alignment_fields x =
        StoneDualityTasteGate_single_carrier_alignment_fields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk zero₁ one₁ meet₁ join₁ compl₁ distributive₁ source₁ pkgRow₁ =>
      cases y with
      | mk zero₂ one₂ meet₂ join₂ compl₂ distributive₂ source₂ pkgRow₂ =>
          injection h with hZero hRest₁
          injection hRest₁ with hOne hRest₂
          injection hRest₂ with hMeet hRest₃
          injection hRest₃ with hJoin hRest₄
          injection hRest₄ with hCompl hRest₅
          injection hRest₅ with hDistributive hRest₆
          injection hRest₆ with hSource hRest₇
          injection hRest₇ with hPkgRow _
          subst hZero
          subst hOne
          subst hMeet
          subst hJoin
          subst hCompl
          subst hDistributive
          subst hSource
          subst hPkgRow
          rfl

instance stoneDualityBHistCarrier : BHistCarrier StoneDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := StoneDualityTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := StoneDualityTasteGate_single_carrier_alignment_fromEventFlow

instance stoneDualityChapterTasteGate : ChapterTasteGate StoneDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      StoneDualityTasteGate_single_carrier_alignment_fromEventFlow
        (StoneDualityTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact StoneDualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StoneDualityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance stoneDualityFieldFaithful : FieldFaithful StoneDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := StoneDualityTasteGate_single_carrier_alignment_fields
  field_faithful := StoneDualityTasteGate_single_carrier_alignment_fields_faithful

instance stoneDualityNontrivial : Nontrivial StoneDualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StoneDualityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      StoneDualityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StoneDualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneDualityChapterTasteGate

theorem StoneDualityTasteGate_single_carrier_alignment :
    (∀ zero one meet join compl distributive source pkgRow : BHist,
      StoneDualityTasteGate_single_carrier_alignment_fields
        (StoneDualityUp.mk zero one meet join compl distributive source pkgRow) =
          [zero, one, meet, join, compl, distributive, source, pkgRow]) ∧
      StoneDualityTasteGate_single_carrier_alignment_encodeBHist (BHist.e0 BHist.Empty) =
        [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro zero one meet join compl distributive source pkgRow
    rfl
  · rfl

end BEDC.Derived.StoneDualityUp
