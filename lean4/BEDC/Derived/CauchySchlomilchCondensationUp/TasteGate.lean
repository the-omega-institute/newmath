import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySchlomilchCondensationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySchlomilchCondensationUp : Type where
  | mk (A M B Q T E H C P N : BHist) : CauchySchlomilchCondensationUp
  deriving DecidableEq

def cauchySchlomilchCondensationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySchlomilchCondensationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySchlomilchCondensationEncodeBHist h

def cauchySchlomilchCondensationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySchlomilchCondensationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySchlomilchCondensationDecodeBHist tail)

private theorem CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchySchlomilchCondensationDecodeBHist
          (cauchySchlomilchCondensationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySchlomilchCondensationFields :
    CauchySchlomilchCondensationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySchlomilchCondensationUp.mk A M B Q T E H C P N =>
      [A, M, B, Q, T, E, H, C, P, N]

def cauchySchlomilchCondensationToEventFlow :
    CauchySchlomilchCondensationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchySchlomilchCondensationFields x).map
      cauchySchlomilchCondensationEncodeBHist

private def cauchySchlomilchCondensationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchySchlomilchCondensationEventAtDefault index rest

def cauchySchlomilchCondensationFromEventFlow
    (ef : EventFlow) : Option CauchySchlomilchCondensationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchySchlomilchCondensationUp.mk
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 0 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 1 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 2 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 3 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 4 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 5 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 6 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 7 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 8 ef))
      (cauchySchlomilchCondensationDecodeBHist
        (cauchySchlomilchCondensationEventAtDefault 9 ef)))

private theorem CauchySchlomilchCondensationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySchlomilchCondensationUp,
      cauchySchlomilchCondensationFromEventFlow
          (cauchySchlomilchCondensationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M B Q T E H C P N =>
      change
        some
          (CauchySchlomilchCondensationUp.mk
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist A))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist M))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist B))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist Q))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist T))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist E))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist H))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist C))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist P))
            (cauchySchlomilchCondensationDecodeBHist
              (cauchySchlomilchCondensationEncodeBHist N))) =
          some (CauchySchlomilchCondensationUp.mk A M B Q T E H C P N)
      rw [CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode A,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode M,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode B,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode Q,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode T,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode E,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode H,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode C,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode P,
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode N]

private theorem
    CauchySchlomilchCondensationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySchlomilchCondensationUp} :
    cauchySchlomilchCondensationToEventFlow x =
        cauchySchlomilchCondensationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySchlomilchCondensationFromEventFlow
          (cauchySchlomilchCondensationToEventFlow x) =
        cauchySchlomilchCondensationFromEventFlow
          (cauchySchlomilchCondensationToEventFlow y) :=
    congrArg cauchySchlomilchCondensationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchySchlomilchCondensationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchySchlomilchCondensationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySchlomilchCondensationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchySchlomilchCondensationUp,
      cauchySchlomilchCondensationFields x = cauchySchlomilchCondensationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ M₁ B₁ Q₁ T₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ M₂ B₂ Q₂ T₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchySchlomilchCondensationBHistCarrier :
    BHistCarrier CauchySchlomilchCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySchlomilchCondensationToEventFlow
  fromEventFlow := cauchySchlomilchCondensationFromEventFlow

instance cauchySchlomilchCondensationChapterTasteGate :
    ChapterTasteGate CauchySchlomilchCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySchlomilchCondensationFromEventFlow
          (cauchySchlomilchCondensationToEventFlow x) =
        some x
    exact CauchySchlomilchCondensationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchySchlomilchCondensationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchySchlomilchCondensationFieldFaithful :
    FieldFaithful CauchySchlomilchCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySchlomilchCondensationFields
  field_faithful :=
    CauchySchlomilchCondensationTasteGate_single_carrier_alignment_fields

instance cauchySchlomilchCondensationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchySchlomilchCondensationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySchlomilchCondensationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySchlomilchCondensationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySchlomilchCondensationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySchlomilchCondensationChapterTasteGate

theorem CauchySchlomilchCondensationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySchlomilchCondensationDecodeBHist
          (cauchySchlomilchCondensationEncodeBHist h) =
        h) ∧
      (∀ x : CauchySchlomilchCondensationUp,
        cauchySchlomilchCondensationFromEventFlow
            (cauchySchlomilchCondensationToEventFlow x) =
          some x) ∧
        (∀ x y : CauchySchlomilchCondensationUp,
          cauchySchlomilchCondensationToEventFlow x =
              cauchySchlomilchCondensationToEventFlow y ->
            x = y) ∧
          cauchySchlomilchCondensationEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchySchlomilchCondensationTasteGate_single_carrier_alignment_decode,
      CauchySchlomilchCondensationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchySchlomilchCondensationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchySchlomilchCondensationUp
