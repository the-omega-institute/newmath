import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeanoContinuumUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeanoContinuumUp : Type where
  | mk (X K S L I R H C Q N : BHist) : PeanoContinuumUp
  deriving DecidableEq

def peanoContinuumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: peanoContinuumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: peanoContinuumEncodeBHist h

def peanoContinuumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (peanoContinuumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (peanoContinuumDecodeBHist tail)

private theorem PeanoContinuumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, peanoContinuumDecodeBHist (peanoContinuumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def peanoContinuumFields : PeanoContinuumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PeanoContinuumUp.mk X K S L I R H C Q N => [X, K, S, L, I, R, H, C, Q, N]

def peanoContinuumToEventFlow : PeanoContinuumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (peanoContinuumFields x).map peanoContinuumEncodeBHist

private def peanoContinuumEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => peanoContinuumEventAt index rest

def peanoContinuumFromEventFlow : EventFlow → Option PeanoContinuumUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PeanoContinuumUp.mk
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 0 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 1 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 2 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 3 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 4 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 5 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 6 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 7 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 8 ef))
          (peanoContinuumDecodeBHist (peanoContinuumEventAt 9 ef)))

private theorem PeanoContinuumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PeanoContinuumUp,
      peanoContinuumFromEventFlow (peanoContinuumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K S L I R H C Q N =>
      change
        some
          (PeanoContinuumUp.mk
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist X))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist K))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist S))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist L))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist I))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist R))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist H))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist C))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist Q))
            (peanoContinuumDecodeBHist (peanoContinuumEncodeBHist N))) =
          some (PeanoContinuumUp.mk X K S L I R H C Q N)
      rw [PeanoContinuumTasteGate_single_carrier_alignment_decode_encode X,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode K,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode S,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode L,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode I,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode R,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode H,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode C,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode Q,
        PeanoContinuumTasteGate_single_carrier_alignment_decode_encode N]

private theorem PeanoContinuumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PeanoContinuumUp} :
    peanoContinuumToEventFlow x = peanoContinuumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      peanoContinuumFromEventFlow (peanoContinuumToEventFlow x) =
        peanoContinuumFromEventFlow (peanoContinuumToEventFlow y) :=
    congrArg peanoContinuumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PeanoContinuumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PeanoContinuumTasteGate_single_carrier_alignment_round_trip y)))

private theorem PeanoContinuumTasteGate_single_carrier_alignment_fields :
    ∀ x y : PeanoContinuumUp, peanoContinuumFields x = peanoContinuumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ K₁ S₁ L₁ I₁ R₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk X₂ K₂ S₂ L₂ I₂ R₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance peanoContinuumBHistCarrier : BHistCarrier PeanoContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := peanoContinuumToEventFlow
  fromEventFlow := peanoContinuumFromEventFlow

instance peanoContinuumChapterTasteGate : ChapterTasteGate PeanoContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change peanoContinuumFromEventFlow (peanoContinuumToEventFlow x) = some x
    exact PeanoContinuumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PeanoContinuumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance peanoContinuumFieldFaithful : FieldFaithful PeanoContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := peanoContinuumFields
  field_faithful := PeanoContinuumTasteGate_single_carrier_alignment_fields

instance peanoContinuumNontrivial : Nontrivial PeanoContinuumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PeanoContinuumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PeanoContinuumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PeanoContinuumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PeanoContinuumUp) ∧
      Nonempty (FieldFaithful PeanoContinuumUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial PeanoContinuumUp) ∧
          (∀ h : BHist, peanoContinuumDecodeBHist (peanoContinuumEncodeBHist h) = h) ∧
            (∀ x : PeanoContinuumUp,
              peanoContinuumFromEventFlow (peanoContinuumToEventFlow x) = some x) ∧
              (∀ x y : PeanoContinuumUp,
                peanoContinuumToEventFlow x = peanoContinuumToEventFlow y → x = y) ∧
                peanoContinuumEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨peanoContinuumChapterTasteGate⟩, ⟨peanoContinuumFieldFaithful⟩,
      ⟨peanoContinuumNontrivial⟩,
      PeanoContinuumTasteGate_single_carrier_alignment_decode_encode,
      PeanoContinuumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PeanoContinuumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PeanoContinuumUp.TasteGate
