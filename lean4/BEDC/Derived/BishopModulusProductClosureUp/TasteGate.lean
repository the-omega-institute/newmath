import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopModulusProductClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopModulusProductClosureUp : Type where
  | mk
      (M_X M_Y Q A B S W_X W_Y D_X D_Y D_Z R_X R_Y U V E H C P N : BHist) :
      BishopModulusProductClosureUp
  deriving DecidableEq

def bishopModulusProductClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopModulusProductClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopModulusProductClosureEncodeBHist h

def bishopModulusProductClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopModulusProductClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopModulusProductClosureDecodeBHist tail)

private theorem BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopModulusProductClosureFields :
    BishopModulusProductClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopModulusProductClosureUp.mk M_X M_Y Q A B S W_X W_Y D_X D_Y D_Z R_X R_Y U V E H C P N =>
      [M_X, M_Y, Q, A, B, S, W_X, W_Y, D_X, D_Y, D_Z, R_X, R_Y, U, V, E, H, C, P, N]

def bishopModulusProductClosureToEventFlow :
    BishopModulusProductClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopModulusProductClosureFields x).map bishopModulusProductClosureEncodeBHist

private def bishopModulusProductClosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopModulusProductClosureEventAt index rest

def bishopModulusProductClosureFromEventFlow (ef : EventFlow) :
    Option BishopModulusProductClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopModulusProductClosureUp.mk
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 0 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 1 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 2 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 3 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 4 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 5 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 6 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 7 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 8 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 9 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 10 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 11 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 12 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 13 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 14 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 15 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 16 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 17 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 18 ef))
      (bishopModulusProductClosureDecodeBHist (bishopModulusProductClosureEventAt 19 ef)))

private theorem BishopModulusProductClosureTasteGate_single_carrier_alignment_round_trip
    (x : BishopModulusProductClosureUp) :
    bishopModulusProductClosureFromEventFlow (bishopModulusProductClosureToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M_X M_Y Q A B S W_X W_Y D_X D_Y D_Z R_X R_Y U V E H C P N =>
      change
        some
          (BishopModulusProductClosureUp.mk
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist M_X))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist M_Y))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist Q))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist A))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist B))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist S))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist W_X))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist W_Y))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist D_X))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist D_Y))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist D_Z))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist R_X))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist R_Y))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist U))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist V))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist E))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist H))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist C))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist P))
            (bishopModulusProductClosureDecodeBHist
              (bishopModulusProductClosureEncodeBHist N))) =
          some
            (BishopModulusProductClosureUp.mk M_X M_Y Q A B S W_X W_Y D_X D_Y D_Z
              R_X R_Y U V E H C P N)
      rw [BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode M_X,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode M_Y,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode Q,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode A,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode B,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode S,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode W_X,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode W_Y,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode D_X,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode D_Y,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode D_Z,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode R_X,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode R_Y,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode U,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode V,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode E,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode H,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode C,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode P,
        BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopModulusProductClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopModulusProductClosureUp} :
    bishopModulusProductClosureToEventFlow x = bishopModulusProductClosureToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopModulusProductClosureFromEventFlow (bishopModulusProductClosureToEventFlow x) =
        bishopModulusProductClosureFromEventFlow (bishopModulusProductClosureToEventFlow y) :=
    congrArg bishopModulusProductClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopModulusProductClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopModulusProductClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopModulusProductClosureTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopModulusProductClosureUp,
      bishopModulusProductClosureFields x = bishopModulusProductClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M_X₁ M_Y₁ Q₁ A₁ B₁ S₁ W_X₁ W_Y₁ D_X₁ D_Y₁ D_Z₁ R_X₁ R_Y₁ U₁ V₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M_X₂ M_Y₂ Q₂ A₂ B₂ S₂ W_X₂ W_Y₂ D_X₂ D_Y₂ D_Z₂ R_X₂ R_Y₂ U₂ V₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopModulusProductClosureBHistCarrier :
    BHistCarrier BishopModulusProductClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopModulusProductClosureToEventFlow
  fromEventFlow := bishopModulusProductClosureFromEventFlow

instance bishopModulusProductClosureChapterTasteGate :
    ChapterTasteGate BishopModulusProductClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopModulusProductClosureFromEventFlow (bishopModulusProductClosureToEventFlow x) =
        some x
    exact BishopModulusProductClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopModulusProductClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopModulusProductClosureFieldFaithful :
    FieldFaithful BishopModulusProductClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopModulusProductClosureFields
  field_faithful := BishopModulusProductClosureTasteGate_single_carrier_alignment_fields_faithful

instance bishopModulusProductClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopModulusProductClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopModulusProductClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopModulusProductClosureUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopModulusProductClosureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopModulusProductClosureUp) ∧
      Nonempty (FieldFaithful BishopModulusProductClosureUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopModulusProductClosureUp) ∧
      (∀ h : BHist,
        bishopModulusProductClosureDecodeBHist
            (bishopModulusProductClosureEncodeBHist h) =
          h) ∧
      (∀ x : BishopModulusProductClosureUp,
        bishopModulusProductClosureFromEventFlow
            (bishopModulusProductClosureToEventFlow x) =
          some x) ∧
      (∀ x y : BishopModulusProductClosureUp,
        bishopModulusProductClosureToEventFlow x = bishopModulusProductClosureToEventFlow y →
          x = y) ∧
      bishopModulusProductClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨bishopModulusProductClosureChapterTasteGate⟩,
      ⟨bishopModulusProductClosureFieldFaithful⟩,
      ⟨bishopModulusProductClosureNontrivial⟩,
      BishopModulusProductClosureTasteGate_single_carrier_alignment_decode_encode,
      BishopModulusProductClosureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopModulusProductClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopModulusProductClosureUp
