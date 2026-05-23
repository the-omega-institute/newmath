import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionMultiplicationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionMultiplicationUp : Type where
  | mk (M O I A S R D E H C P N : BHist) : CauchyCompletionMultiplicationUp
  deriving DecidableEq

def cauchyCompletionMultiplicationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionMultiplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionMultiplicationEncodeBHist h

def cauchyCompletionMultiplicationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionMultiplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionMultiplicationDecodeBHist tail)

private theorem CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchyCompletionMultiplicationDecodeBHist
          (cauchyCompletionMultiplicationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionMultiplicationFields :
    CauchyCompletionMultiplicationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionMultiplicationUp.mk M O I A S R D E H C P N =>
      [M, O, I, A, S, R, D, E, H, C, P, N]

def cauchyCompletionMultiplicationToEventFlow :
    CauchyCompletionMultiplicationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionMultiplicationFields x).map
      cauchyCompletionMultiplicationEncodeBHist

private def cauchyCompletionMultiplicationEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionMultiplicationEventAtDefault index rest

def cauchyCompletionMultiplicationFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionMultiplicationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionMultiplicationUp.mk
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 0 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 1 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 2 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 3 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 4 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 5 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 6 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 7 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 8 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 9 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 10 ef))
      (cauchyCompletionMultiplicationDecodeBHist
        (cauchyCompletionMultiplicationEventAtDefault 11 ef)))

private theorem CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyCompletionMultiplicationUp,
      cauchyCompletionMultiplicationFromEventFlow
          (cauchyCompletionMultiplicationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M O I A S R D E H C P N =>
      change
        some
          (CauchyCompletionMultiplicationUp.mk
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist M))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist O))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist I))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist A))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist S))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist R))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist D))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist E))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist H))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist C))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist P))
            (cauchyCompletionMultiplicationDecodeBHist
              (cauchyCompletionMultiplicationEncodeBHist N))) =
          some (CauchyCompletionMultiplicationUp.mk M O I A S R D E H C P N)
      rw [CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode M,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode O,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode I,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode A,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionMultiplicationUp} :
    cauchyCompletionMultiplicationToEventFlow x =
        cauchyCompletionMultiplicationToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionMultiplicationFromEventFlow
          (cauchyCompletionMultiplicationToEventFlow x) =
        cauchyCompletionMultiplicationFromEventFlow
          (cauchyCompletionMultiplicationToEventFlow y) :=
    congrArg cauchyCompletionMultiplicationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_fields :
    forall x y : CauchyCompletionMultiplicationUp,
      cauchyCompletionMultiplicationFields x =
          cauchyCompletionMultiplicationFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance cauchyCompletionMultiplicationBHistCarrier :
    BHistCarrier CauchyCompletionMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionMultiplicationToEventFlow
  fromEventFlow := cauchyCompletionMultiplicationFromEventFlow

instance cauchyCompletionMultiplicationChapterTasteGate :
    ChapterTasteGate CauchyCompletionMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionMultiplicationFromEventFlow
          (cauchyCompletionMultiplicationToEventFlow x) =
        some x
    exact CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyCompletionMultiplicationFieldFaithful :
    FieldFaithful CauchyCompletionMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionMultiplicationFields
  field_faithful :=
    CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_fields

instance cauchyCompletionMultiplicationNontrivial :
    Nontrivial CauchyCompletionMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionMultiplicationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionMultiplicationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletionMultiplicationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionMultiplicationUp) ∧
      Nonempty (FieldFaithful CauchyCompletionMultiplicationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionMultiplicationUp) ∧
      (∀ h : BHist,
        cauchyCompletionMultiplicationDecodeBHist
            (cauchyCompletionMultiplicationEncodeBHist h) =
          h) ∧
      (∀ x : CauchyCompletionMultiplicationUp,
        cauchyCompletionMultiplicationFromEventFlow
            (cauchyCompletionMultiplicationToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionMultiplicationUp,
        cauchyCompletionMultiplicationToEventFlow x =
            cauchyCompletionMultiplicationToEventFlow y ->
          x = y) ∧
      cauchyCompletionMultiplicationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyCompletionMultiplicationChapterTasteGate⟩,
      ⟨cauchyCompletionMultiplicationFieldFaithful⟩,
      ⟨cauchyCompletionMultiplicationNontrivial⟩,
      CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_decode,
      CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyCompletionMultiplicationTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp.TasteGate
