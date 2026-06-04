import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareBoundaryFixedTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareBoundaryFixedTransportUp : Type where
  | mk (D F M T P R H C A N : BHist) : PoincareBoundaryFixedTransportUp
  deriving DecidableEq

def poincareBoundaryFixedTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareBoundaryFixedTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareBoundaryFixedTransportEncodeBHist h

def poincareBoundaryFixedTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareBoundaryFixedTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareBoundaryFixedTransportDecodeBHist tail)

private theorem PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def poincareBoundaryFixedTransportFields :
    PoincareBoundaryFixedTransportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareBoundaryFixedTransportUp.mk D F M T P R H C A N =>
      [D, F, M, T, P, R, H, C, A, N]

def poincareBoundaryFixedTransportToEventFlow :
    PoincareBoundaryFixedTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (poincareBoundaryFixedTransportFields x).map
        poincareBoundaryFixedTransportEncodeBHist

private def poincareBoundaryFixedTransportEventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      poincareBoundaryFixedTransportEventAt index rest

def poincareBoundaryFixedTransportFromEventFlow
    (ef : EventFlow) : Option PoincareBoundaryFixedTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PoincareBoundaryFixedTransportUp.mk
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 0 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 1 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 2 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 3 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 4 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 5 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 6 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 7 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 8 ef))
      (poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEventAt 9 ef)))

private theorem PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_round_trip
    (x : PoincareBoundaryFixedTransportUp) :
    poincareBoundaryFixedTransportFromEventFlow
      (poincareBoundaryFixedTransportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D F M T P R H C A N =>
      change
        some
          (PoincareBoundaryFixedTransportUp.mk
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist D))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist F))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist M))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist T))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist P))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist R))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist H))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist C))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist A))
            (poincareBoundaryFixedTransportDecodeBHist
              (poincareBoundaryFixedTransportEncodeBHist N))) =
          some (PoincareBoundaryFixedTransportUp.mk D F M T P R H C A N)
      rw [PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode D,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode F,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode M,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode T,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode P,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode R,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode H,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode C,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode A,
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode N]

private theorem PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_injective
    {x y : PoincareBoundaryFixedTransportUp} :
    poincareBoundaryFixedTransportToEventFlow x =
      poincareBoundaryFixedTransportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareBoundaryFixedTransportFromEventFlow
          (poincareBoundaryFixedTransportToEventFlow x) =
        poincareBoundaryFixedTransportFromEventFlow
          (poincareBoundaryFixedTransportToEventFlow y) :=
    congrArg poincareBoundaryFixedTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_round_trip y)))

private theorem PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_fields :
    ∀ x y : PoincareBoundaryFixedTransportUp,
      poincareBoundaryFixedTransportFields x =
        poincareBoundaryFixedTransportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ F₁ M₁ T₁ P₁ R₁ H₁ C₁ A₁ N₁ =>
      cases y with
      | mk D₂ F₂ M₂ T₂ P₂ R₂ H₂ C₂ A₂ N₂ =>
          cases hfields
          rfl

instance poincareBoundaryFixedTransportBHistCarrier :
    BHistCarrier PoincareBoundaryFixedTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareBoundaryFixedTransportToEventFlow
  fromEventFlow := poincareBoundaryFixedTransportFromEventFlow

instance poincareBoundaryFixedTransportChapterTasteGate :
    ChapterTasteGate PoincareBoundaryFixedTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      poincareBoundaryFixedTransportFromEventFlow
        (poincareBoundaryFixedTransportToEventFlow x) = some x
    exact PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_injective heq)

instance poincareBoundaryFixedTransportFieldFaithful :
    FieldFaithful PoincareBoundaryFixedTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := poincareBoundaryFixedTransportFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    exact PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_fields x y h

instance poincareBoundaryFixedTransportNontrivial :
    Nontrivial PoincareBoundaryFixedTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoincareBoundaryFixedTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PoincareBoundaryFixedTransportUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hD _ _ _ _ _ _ _ _ _
        cases hD⟩

theorem PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      poincareBoundaryFixedTransportDecodeBHist
        (poincareBoundaryFixedTransportEncodeBHist h) = h) ∧
      (∀ x : PoincareBoundaryFixedTransportUp,
        poincareBoundaryFixedTransportFromEventFlow
          (poincareBoundaryFixedTransportToEventFlow x) = some x) ∧
        (∀ x y : PoincareBoundaryFixedTransportUp,
          poincareBoundaryFixedTransportToEventFlow x =
            poincareBoundaryFixedTransportToEventFlow y -> x = y) ∧
          poincareBoundaryFixedTransportEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : PoincareBoundaryFixedTransportUp,
              poincareBoundaryFixedTransportFields x =
                poincareBoundaryFixedTransportFields y -> x = y) ∧
              (∃ x y : PoincareBoundaryFixedTransportUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_decode,
      PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_injective heq),
      rfl,
      PoincareBoundaryFixedTransportTasteGate_single_carrier_alignment_fields,
      ⟨PoincareBoundaryFixedTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        PoincareBoundaryFixedTransportUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          injection h with hD _ _ _ _ _ _ _ _ _
          cases hD⟩⟩

end BEDC.Derived.PoincareBoundaryFixedTransportUp
