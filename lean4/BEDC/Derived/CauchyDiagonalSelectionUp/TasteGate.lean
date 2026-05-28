import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDiagonalSelectionUp : Type where
  | mk (S R M W T E H C P N : BHist) : CauchyDiagonalSelectionUp
  deriving DecidableEq

def cauchyDiagonalSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalSelectionEncodeBHist h

def cauchyDiagonalSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalSelectionDecodeBHist tail)

private theorem cauchyDiagonalSelection_decode_encode_bhist :
    ∀ h : BHist,
      cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDiagonalSelectionToEventFlow : CauchyDiagonalSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalSelectionUp.mk S R M W T E H C P N =>
      [cauchyDiagonalSelectionEncodeBHist S,
        cauchyDiagonalSelectionEncodeBHist R,
        cauchyDiagonalSelectionEncodeBHist M,
        cauchyDiagonalSelectionEncodeBHist W,
        cauchyDiagonalSelectionEncodeBHist T,
        cauchyDiagonalSelectionEncodeBHist E,
        cauchyDiagonalSelectionEncodeBHist H,
        cauchyDiagonalSelectionEncodeBHist C,
        cauchyDiagonalSelectionEncodeBHist P,
        cauchyDiagonalSelectionEncodeBHist N]

private def cauchyDiagonalSelectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyDiagonalSelectionEventAtDefault index rest

def cauchyDiagonalSelectionFromEventFlow
    (ef : EventFlow) : Option CauchyDiagonalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyDiagonalSelectionUp.mk
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 0 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 1 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 2 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 3 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 4 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 5 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 6 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 7 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 8 ef))
      (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEventAtDefault 9 ef)))

private theorem cauchyDiagonalSelection_round_trip :
    ∀ x : CauchyDiagonalSelectionUp,
      cauchyDiagonalSelectionFromEventFlow (cauchyDiagonalSelectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M W T E H C P N =>
      change
        some
            (CauchyDiagonalSelectionUp.mk
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist S))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist R))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist M))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist W))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist T))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist E))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist H))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist C))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist P))
              (cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist N))) =
          some (CauchyDiagonalSelectionUp.mk S R M W T E H C P N)
      rw [cauchyDiagonalSelection_decode_encode_bhist S,
        cauchyDiagonalSelection_decode_encode_bhist R,
        cauchyDiagonalSelection_decode_encode_bhist M,
        cauchyDiagonalSelection_decode_encode_bhist W,
        cauchyDiagonalSelection_decode_encode_bhist T,
        cauchyDiagonalSelection_decode_encode_bhist E,
        cauchyDiagonalSelection_decode_encode_bhist H,
        cauchyDiagonalSelection_decode_encode_bhist C,
        cauchyDiagonalSelection_decode_encode_bhist P,
        cauchyDiagonalSelection_decode_encode_bhist N]

private theorem cauchyDiagonalSelectionToEventFlow_injective
    {x y : CauchyDiagonalSelectionUp} :
    cauchyDiagonalSelectionToEventFlow x = cauchyDiagonalSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalSelectionFromEventFlow (cauchyDiagonalSelectionToEventFlow x) =
        cauchyDiagonalSelectionFromEventFlow (cauchyDiagonalSelectionToEventFlow y) :=
    congrArg cauchyDiagonalSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDiagonalSelection_round_trip x).symm
      (Eq.trans hread (cauchyDiagonalSelection_round_trip y)))

def cauchyDiagonalSelectionFields : CauchyDiagonalSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalSelectionUp.mk S R M W T E H C P N => [S, R, M, W, T, E, H, C, P, N]

private theorem cauchyDiagonalSelection_fields_faithful :
    ∀ x y : CauchyDiagonalSelectionUp,
      cauchyDiagonalSelectionFields x = cauchyDiagonalSelectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S R M W T E H C P N =>
      cases y with
      | mk S' R' M' W' T' E' H' C' P' N' =>
          simp only [cauchyDiagonalSelectionFields] at h
          cases h
          rfl

instance cauchyDiagonalSelectionBHistCarrier : BHistCarrier CauchyDiagonalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalSelectionToEventFlow
  fromEventFlow := cauchyDiagonalSelectionFromEventFlow

instance cauchyDiagonalSelectionChapterTasteGate :
    ChapterTasteGate CauchyDiagonalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDiagonalSelectionFromEventFlow (cauchyDiagonalSelectionToEventFlow x) = some x
    exact cauchyDiagonalSelection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDiagonalSelectionToEventFlow_injective heq)

instance cauchyDiagonalSelectionFieldFaithful : FieldFaithful CauchyDiagonalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyDiagonalSelectionFields
  field_faithful := cauchyDiagonalSelection_fields_faithful

instance cauchyDiagonalSelectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyDiagonalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyDiagonalSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyDiagonalSelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyDiagonalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDiagonalSelectionChapterTasteGate

theorem CauchyDiagonalSelectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyDiagonalSelectionUp) ∧
      Nonempty (FieldFaithful CauchyDiagonalSelectionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyDiagonalSelectionUp) ∧
          (∀ h : BHist,
            cauchyDiagonalSelectionDecodeBHist (cauchyDiagonalSelectionEncodeBHist h) = h) ∧
            (∀ x : CauchyDiagonalSelectionUp,
              cauchyDiagonalSelectionFromEventFlow (cauchyDiagonalSelectionToEventFlow x) =
                some x) ∧
              (∀ x y : CauchyDiagonalSelectionUp,
                cauchyDiagonalSelectionToEventFlow x =
                    cauchyDiagonalSelectionToEventFlow y →
                  x = y) ∧
                cauchyDiagonalSelectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyDiagonalSelectionChapterTasteGate⟩,
      ⟨cauchyDiagonalSelectionFieldFaithful⟩,
      ⟨cauchyDiagonalSelectionNontrivial⟩,
      cauchyDiagonalSelection_decode_encode_bhist,
      cauchyDiagonalSelection_round_trip,
      (fun _ _ heq => cauchyDiagonalSelectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyDiagonalSelectionUp
