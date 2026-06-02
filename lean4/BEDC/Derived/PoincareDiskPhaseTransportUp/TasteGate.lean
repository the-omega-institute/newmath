import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareDiskPhaseTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareDiskPhaseTransportUp : Type where
  | mk (L Z U B Gamma V F O A H C R N : BHist) : PoincareDiskPhaseTransportUp
  deriving DecidableEq

def poincareDiskPhaseTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareDiskPhaseTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareDiskPhaseTransportEncodeBHist h

def poincareDiskPhaseTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareDiskPhaseTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareDiskPhaseTransportDecodeBHist tail)

private theorem PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      poincareDiskPhaseTransportDecodeBHist (poincareDiskPhaseTransportEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareDiskPhaseTransportFields :
    PoincareDiskPhaseTransportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareDiskPhaseTransportUp.mk L Z U B Gamma V F O A H C R N =>
      [L, Z, U, B, Gamma, V, F, O, A, H, C, R, N]

def poincareDiskPhaseTransportToEventFlow :
    PoincareDiskPhaseTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareDiskPhaseTransportFields x).map poincareDiskPhaseTransportEncodeBHist

private def poincareDiskPhaseTransportEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      poincareDiskPhaseTransportEventAtDefault index rest

def poincareDiskPhaseTransportFromEventFlow
    (ef : EventFlow) : Option PoincareDiskPhaseTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PoincareDiskPhaseTransportUp.mk
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 0 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 1 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 2 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 3 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 4 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 5 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 6 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 7 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 8 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 9 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 10 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 11 ef))
      (poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEventAtDefault 12 ef)))

private theorem PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_round_trip
    (x : PoincareDiskPhaseTransportUp) :
    poincareDiskPhaseTransportFromEventFlow
      (poincareDiskPhaseTransportToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L Z U B Gamma V F O A H C R N =>
      change
        some
          (PoincareDiskPhaseTransportUp.mk
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist L))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist Z))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist U))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist B))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist Gamma))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist V))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist F))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist O))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist A))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist H))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist C))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist R))
            (poincareDiskPhaseTransportDecodeBHist
              (poincareDiskPhaseTransportEncodeBHist N))) =
          some (PoincareDiskPhaseTransportUp.mk L Z U B Gamma V F O A H C R N)
      rw [PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode L,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode Z,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode U,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode B,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode Gamma,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode V,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode F,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode O,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode A,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode H,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode C,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode R,
        PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode N]

private theorem PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_injective
    {x y : PoincareDiskPhaseTransportUp} :
    poincareDiskPhaseTransportToEventFlow x = poincareDiskPhaseTransportToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareDiskPhaseTransportFromEventFlow
          (poincareDiskPhaseTransportToEventFlow x) =
        poincareDiskPhaseTransportFromEventFlow
          (poincareDiskPhaseTransportToEventFlow y) :=
    congrArg poincareDiskPhaseTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_round_trip y)))

private theorem PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_fields :
    ∀ x y : PoincareDiskPhaseTransportUp,
      poincareDiskPhaseTransportFields x = poincareDiskPhaseTransportFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ Z₁ U₁ B₁ Gamma₁ V₁ F₁ O₁ A₁ H₁ C₁ R₁ N₁ =>
      cases y with
      | mk L₂ Z₂ U₂ B₂ Gamma₂ V₂ F₂ O₂ A₂ H₂ C₂ R₂ N₂ =>
          cases hfields
          rfl

instance poincareDiskPhaseTransportBHistCarrier :
    BHistCarrier PoincareDiskPhaseTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareDiskPhaseTransportToEventFlow
  fromEventFlow := poincareDiskPhaseTransportFromEventFlow

instance poincareDiskPhaseTransportChapterTasteGate :
    ChapterTasteGate PoincareDiskPhaseTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      poincareDiskPhaseTransportFromEventFlow
        (poincareDiskPhaseTransportToEventFlow x) = some x
    exact PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_injective heq)

instance poincareDiskPhaseTransportFieldFaithful :
    FieldFaithful PoincareDiskPhaseTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := poincareDiskPhaseTransportFields
  field_faithful :=
    PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_fields

instance poincareDiskPhaseTransportNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PoincareDiskPhaseTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoincareDiskPhaseTransportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PoincareDiskPhaseTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PoincareDiskPhaseTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  poincareDiskPhaseTransportChapterTasteGate

theorem PoincareDiskPhaseTransportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      poincareDiskPhaseTransportDecodeBHist
        (poincareDiskPhaseTransportEncodeBHist h) = h) ∧
      (∀ x : PoincareDiskPhaseTransportUp,
        poincareDiskPhaseTransportFromEventFlow
          (poincareDiskPhaseTransportToEventFlow x) =
            some x) ∧
        (∀ x y : PoincareDiskPhaseTransportUp,
          poincareDiskPhaseTransportToEventFlow x =
            poincareDiskPhaseTransportToEventFlow y →
              x = y) ∧
          poincareDiskPhaseTransportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PoincareDiskPhaseTransportTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.PoincareDiskPhaseTransportUp
