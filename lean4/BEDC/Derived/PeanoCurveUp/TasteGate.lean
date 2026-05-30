import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeanoCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeanoCurveUp : Type where
  | mk (I G S X Y E R H C Q N : BHist) : PeanoCurveUp
  deriving DecidableEq

def peanoCurveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: peanoCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: peanoCurveEncodeBHist h

def peanoCurveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (peanoCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (peanoCurveDecodeBHist tail)

private theorem PeanoCurveTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, peanoCurveDecodeBHist (peanoCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def peanoCurveFields : PeanoCurveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoCurveUp.mk I G S X Y E R H C Q N => [I, G, S, X, Y, E, R, H, C, Q, N]

def peanoCurveToEventFlow : PeanoCurveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (peanoCurveFields x).map peanoCurveEncodeBHist

private def PeanoCurveTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      PeanoCurveTasteGate_single_carrier_alignment_eventAt index rest

def peanoCurveFromEventFlow (ef : EventFlow) : Option PeanoCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PeanoCurveUp.mk
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 0 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 1 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 2 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 3 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 4 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 5 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 6 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 7 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 8 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 9 ef))
      (peanoCurveDecodeBHist (PeanoCurveTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem PeanoCurveTasteGate_single_carrier_alignment_round_trip
    (x : PeanoCurveUp) :
    peanoCurveFromEventFlow (peanoCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G S X Y E R H C Q N =>
      change
        some
          (PeanoCurveUp.mk
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist I))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist G))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist S))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist X))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist Y))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist E))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist R))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist H))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist C))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist Q))
            (peanoCurveDecodeBHist (peanoCurveEncodeBHist N))) =
          some (PeanoCurveUp.mk I G S X Y E R H C Q N)
      rw [PeanoCurveTasteGate_single_carrier_alignment_decode_encode I,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode G,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode S,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode X,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode Y,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode E,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode R,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode H,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode C,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode Q,
        PeanoCurveTasteGate_single_carrier_alignment_decode_encode N]

private theorem PeanoCurveTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PeanoCurveUp} :
    peanoCurveToEventFlow x = peanoCurveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      peanoCurveFromEventFlow (peanoCurveToEventFlow x) =
        peanoCurveFromEventFlow (peanoCurveToEventFlow y) :=
    congrArg peanoCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PeanoCurveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PeanoCurveTasteGate_single_carrier_alignment_round_trip y)))

private theorem PeanoCurveTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PeanoCurveUp, peanoCurveFields x = peanoCurveFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ G₁ S₁ X₁ Y₁ E₁ R₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk I₂ G₂ S₂ X₂ Y₂ E₂ R₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance peanoCurveBHistCarrier : BHistCarrier PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := peanoCurveToEventFlow
  fromEventFlow := peanoCurveFromEventFlow

instance peanoCurveChapterTasteGate : ChapterTasteGate PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change peanoCurveFromEventFlow (peanoCurveToEventFlow x) = some x
    exact PeanoCurveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PeanoCurveTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance peanoCurveFieldFaithful : FieldFaithful PeanoCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := peanoCurveFields
  field_faithful := PeanoCurveTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate PeanoCurveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  peanoCurveChapterTasteGate

theorem PeanoCurveTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PeanoCurveUp) ∧
      Nonempty (ChapterTasteGate PeanoCurveUp) ∧
        Nonempty (FieldFaithful PeanoCurveUp) ∧
          (∀ h : BHist, peanoCurveDecodeBHist (peanoCurveEncodeBHist h) = h) ∧
            (∀ x : PeanoCurveUp,
              peanoCurveFromEventFlow (peanoCurveToEventFlow x) = some x) ∧
              (∀ x y : PeanoCurveUp,
                peanoCurveToEventFlow x = peanoCurveToEventFlow y → x = y) ∧
                peanoCurveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨peanoCurveBHistCarrier⟩,
      ⟨peanoCurveChapterTasteGate⟩,
      ⟨peanoCurveFieldFaithful⟩,
      PeanoCurveTasteGate_single_carrier_alignment_decode_encode,
      PeanoCurveTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PeanoCurveTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PeanoCurveUp
