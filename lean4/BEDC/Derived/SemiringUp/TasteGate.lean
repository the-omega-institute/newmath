import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SemiringUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SemiringUp : Type where
  | mk (A M Z D E H C P N : BHist) : SemiringUp
  deriving DecidableEq

def SemiringTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def SemiringTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: SemiringTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: SemiringTasteGate_single_carrier_alignment_encodeBHist h

def SemiringTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (SemiringTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (SemiringTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SemiringTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      SemiringTasteGate_single_carrier_alignment_decodeBHist
          (SemiringTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SemiringTasteGate_single_carrier_alignment_fields : SemiringUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SemiringUp.mk A M Z D E H C P N => [A, M, Z, D, E, H, C, P, N]

def SemiringTasteGate_single_carrier_alignment_toEventFlow : SemiringUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SemiringUp.mk A M Z D E H C P N =>
      [SemiringTasteGate_single_carrier_alignment_tag,
        SemiringTasteGate_single_carrier_alignment_encodeBHist A,
        SemiringTasteGate_single_carrier_alignment_encodeBHist M,
        SemiringTasteGate_single_carrier_alignment_encodeBHist Z,
        SemiringTasteGate_single_carrier_alignment_encodeBHist D,
        SemiringTasteGate_single_carrier_alignment_encodeBHist E,
        SemiringTasteGate_single_carrier_alignment_encodeBHist H,
        SemiringTasteGate_single_carrier_alignment_encodeBHist C,
        SemiringTasteGate_single_carrier_alignment_encodeBHist P,
        SemiringTasteGate_single_carrier_alignment_encodeBHist N]

private def SemiringTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => SemiringTasteGate_single_carrier_alignment_eventAt index rest

def SemiringTasteGate_single_carrier_alignment_fromEventFlow : EventFlow → Option SemiringUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SemiringUp.mk
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 1 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 2 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 3 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 4 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 5 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 6 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 7 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 8 ef))
          (SemiringTasteGate_single_carrier_alignment_decodeBHist
            (SemiringTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem SemiringTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SemiringUp,
      SemiringTasteGate_single_carrier_alignment_fromEventFlow
          (SemiringTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M Z D E H C P N =>
      change
        some
          (SemiringUp.mk
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist A))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist M))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist Z))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist D))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist E))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist H))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist C))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist P))
            (SemiringTasteGate_single_carrier_alignment_decodeBHist
              (SemiringTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SemiringUp.mk A M Z D E H C P N)
      rw [SemiringTasteGate_single_carrier_alignment_decode A,
        SemiringTasteGate_single_carrier_alignment_decode M,
        SemiringTasteGate_single_carrier_alignment_decode Z,
        SemiringTasteGate_single_carrier_alignment_decode D,
        SemiringTasteGate_single_carrier_alignment_decode E,
        SemiringTasteGate_single_carrier_alignment_decode H,
        SemiringTasteGate_single_carrier_alignment_decode C,
        SemiringTasteGate_single_carrier_alignment_decode P,
        SemiringTasteGate_single_carrier_alignment_decode N]

private theorem SemiringTasteGate_single_carrier_alignment_injective {x y : SemiringUp} :
    SemiringTasteGate_single_carrier_alignment_toEventFlow x =
        SemiringTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SemiringTasteGate_single_carrier_alignment_fromEventFlow
          (SemiringTasteGate_single_carrier_alignment_toEventFlow x) =
        SemiringTasteGate_single_carrier_alignment_fromEventFlow
          (SemiringTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SemiringTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SemiringTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SemiringTasteGate_single_carrier_alignment_round_trip y)))

private theorem SemiringTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SemiringUp,
      SemiringTasteGate_single_carrier_alignment_fields x =
          SemiringTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ M₁ Z₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ M₂ Z₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance SemiringTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SemiringTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SemiringTasteGate_single_carrier_alignment_fromEventFlow

instance SemiringTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SemiringTasteGate_single_carrier_alignment_fromEventFlow
          (SemiringTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact SemiringTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SemiringTasteGate_single_carrier_alignment_injective heq)

instance SemiringTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SemiringTasteGate_single_carrier_alignment_fields
  field_faithful := SemiringTasteGate_single_carrier_alignment_fields_faithful

instance SemiringTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial SemiringUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SemiringUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      SemiringUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SemiringTasteGate_single_carrier_alignment :
    (forall h : BHist,
      SemiringTasteGate_single_carrier_alignment_decodeBHist
        (SemiringTasteGate_single_carrier_alignment_encodeBHist h) = h) /\
      SemiringTasteGate_single_carrier_alignment_fields
        (SemiringUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty] /\
        SemiringTasteGate_single_carrier_alignment_toEventFlow
          (SemiringUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SemiringTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.SemiringUp
