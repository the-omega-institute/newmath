import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveDiniTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveDiniTheoremUp : Type where
  | mk (K F M D U W R E H C P N : BHist) : ConstructiveDiniTheoremUp
  deriving DecidableEq

def constructiveDiniTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveDiniTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveDiniTheoremEncodeBHist h

def constructiveDiniTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveDiniTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveDiniTheoremDecodeBHist tail)

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def constructiveDiniTheoremFields : ConstructiveDiniTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveDiniTheoremUp.mk K F M D U W R E H C P N =>
      [K, F, M, D, U, W, R, E, H, C, P, N]

def constructiveDiniTheoremToEventFlow : ConstructiveDiniTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveDiniTheoremFields x).map constructiveDiniTheoremEncodeBHist

private def ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt index rest

private def ConstructiveDiniTheoremTasteGate_single_carrier_alignment_lengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest =>
      ConstructiveDiniTheoremTasteGate_single_carrier_alignment_lengthEq index rest

def constructiveDiniTheoremFromEventFlow :
    EventFlow → Option ConstructiveDiniTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match ConstructiveDiniTheoremTasteGate_single_carrier_alignment_lengthEq 12 flow with
      | true =>
          some
            (ConstructiveDiniTheoremUp.mk
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 0 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 1 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 2 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 3 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 4 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 5 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 6 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 7 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 8 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 9 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 10 flow))
              (constructiveDiniTheoremDecodeBHist
                (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_rawAt 11 flow)))
      | false => none

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveDiniTheoremUp,
      constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) = some x :=
  by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M D U W R E H C P N =>
      change
        some
          (ConstructiveDiniTheoremUp.mk
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist K))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist F))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist M))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist D))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist U))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist W))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist R))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist E))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist H))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist C))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist P))
            (constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist N))) =
          some (ConstructiveDiniTheoremUp.mk K F M D U W R E H C P N)
      rw [ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode K,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode F,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode M,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode D,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode U,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode W,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode R,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode E,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode H,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode C,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode P,
        ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_injective
    {x y : ConstructiveDiniTheoremUp} :
    constructiveDiniTheoremToEventFlow x = constructiveDiniTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) =
        constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow y) :=
    congrArg constructiveDiniTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ConstructiveDiniTheoremUp,
      constructiveDiniTheoremFields x = constructiveDiniTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ M₁ D₁ U₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ M₂ D₂ U₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hF tail1
          injection tail1 with hM tail2
          injection tail2 with hD tail3
          injection tail3 with hU tail4
          injection tail4 with hW tail5
          injection tail5 with hR tail6
          injection tail6 with hE tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hK
          subst hF
          subst hM
          subst hD
          subst hU
          subst hW
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance constructiveDiniTheoremBHistCarrier : BHistCarrier ConstructiveDiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveDiniTheoremToEventFlow
  fromEventFlow := constructiveDiniTheoremFromEventFlow

instance constructiveDiniTheoremChapterTasteGate :
    ChapterTasteGate ConstructiveDiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) = some x
    exact ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveDiniTheoremTasteGate_single_carrier_alignment_injective heq)

instance constructiveDiniTheoremFieldFaithful :
    FieldFaithful ConstructiveDiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveDiniTheoremFields
  field_faithful :=
    ConstructiveDiniTheoremTasteGate_single_carrier_alignment_fields_faithful

theorem ConstructiveDiniTheoremTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConstructiveDiniTheoremUp) ∧
      Nonempty (FieldFaithful ConstructiveDiniTheoremUp) ∧
        (∀ h : BHist,
          constructiveDiniTheoremDecodeBHist (constructiveDiniTheoremEncodeBHist h) = h) ∧
          (∀ x : ConstructiveDiniTheoremUp,
            constructiveDiniTheoremFromEventFlow (constructiveDiniTheoremToEventFlow x) =
              some x) ∧
            constructiveDiniTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨constructiveDiniTheoremChapterTasteGate⟩,
      ⟨constructiveDiniTheoremFieldFaithful⟩,
      ConstructiveDiniTheoremTasteGate_single_carrier_alignment_decode,
      ConstructiveDiniTheoremTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.ConstructiveDiniTheoremUp
