import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwarzLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwarzLemmaUp : Type where
  | mk (H D Z B M R T P N : BHist) : SchwarzLemmaUp
  deriving DecidableEq

def SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist h

def SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
          (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SchwarzLemmaTasteGate_single_carrier_alignment_fields :
    SchwarzLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwarzLemmaUp.mk H D Z B M R T P N => [H, D, Z, B, M, R, T, P, N]

def SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow :
    SchwarzLemmaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (SchwarzLemmaTasteGate_single_carrier_alignment_fields x).map
      SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist

private def SchwarzLemmaTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => SchwarzLemmaTasteGate_single_carrier_alignment_eventAt index rest

def SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option SchwarzLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SchwarzLemmaUp.mk
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 0 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 1 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 2 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 3 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 4 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 5 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 6 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 7 ef))
      (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
        (SchwarzLemmaTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem SchwarzLemmaTasteGate_single_carrier_alignment_round_trip
    (x : SchwarzLemmaUp) :
    SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow
        (SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H D Z B M R T P N =>
      change
        some
          (SchwarzLemmaUp.mk
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist H))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist D))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist Z))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist B))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist M))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist R))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist T))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist P))
            (SchwarzLemmaTasteGate_single_carrier_alignment_decodeBHist
              (SchwarzLemmaTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SchwarzLemmaUp.mk H D Z B M R T P N)
      rw [SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode H,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode D,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode Z,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode B,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode M,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode R,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode T,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode P,
        SchwarzLemmaTasteGate_single_carrier_alignment_decode_encode N]

private theorem SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchwarzLemmaUp} :
    SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow x =
        SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow
          (SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow x) =
        SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow
          (SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SchwarzLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SchwarzLemmaTasteGate_single_carrier_alignment_round_trip y)))

private theorem SchwarzLemmaTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SchwarzLemmaUp,
      SchwarzLemmaTasteGate_single_carrier_alignment_fields x =
          SchwarzLemmaTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ D₁ Z₁ B₁ M₁ R₁ T₁ P₁ N₁ =>
      cases y with
      | mk H₂ D₂ Z₂ B₂ M₂ R₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance SchwarzLemmaTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow

instance SchwarzLemmaTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      SchwarzLemmaTasteGate_single_carrier_alignment_fromEventFlow
          (SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact SchwarzLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchwarzLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance SchwarzLemmaTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SchwarzLemmaTasteGate_single_carrier_alignment_fields
  field_faithful := SchwarzLemmaTasteGate_single_carrier_alignment_fields_faithful

instance SchwarzLemmaTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial SchwarzLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchwarzLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SchwarzLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchwarzLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SchwarzLemmaTasteGate_single_carrier_alignment_ChapterTasteGate

namespace TasteGate

theorem SchwarzLemmaTasteGate_single_carrier_alignment :
    ChapterTasteGate SchwarzLemmaUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact taste_gate

end TasteGate

end BEDC.Derived.SchwarzLemmaUp
