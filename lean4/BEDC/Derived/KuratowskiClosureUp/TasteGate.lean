import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiClosureUp : Type where
  | mk (T S N W Q H C P L : BHist) : KuratowskiClosureUp
  deriving DecidableEq

def kuratowskiClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiClosureEncodeBHist h

def kuratowskiClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiClosureDecodeBHist tail)

private theorem KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiClosureFields : KuratowskiClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiClosureUp.mk T S N W Q H C P L => [T, S, N, W, Q, H, C, P, L]

def kuratowskiClosureToEventFlow : KuratowskiClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiClosureFields x).map kuratowskiClosureEncodeBHist

def kuratowskiClosureFromEventFlow : EventFlow → Option KuratowskiClosureUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: S :: N :: W :: Q :: H :: C :: P :: L :: [] =>
      some
        (KuratowskiClosureUp.mk
          (kuratowskiClosureDecodeBHist T)
          (kuratowskiClosureDecodeBHist S)
          (kuratowskiClosureDecodeBHist N)
          (kuratowskiClosureDecodeBHist W)
          (kuratowskiClosureDecodeBHist Q)
          (kuratowskiClosureDecodeBHist H)
          (kuratowskiClosureDecodeBHist C)
          (kuratowskiClosureDecodeBHist P)
          (kuratowskiClosureDecodeBHist L))
  | _ => none

private theorem KuratowskiClosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KuratowskiClosureUp,
      kuratowskiClosureFromEventFlow (kuratowskiClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S N W Q H C P L =>
      change
        some
          (KuratowskiClosureUp.mk
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist T))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist S))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist N))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist W))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist Q))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist H))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist C))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist P))
            (kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist L))) =
          some (KuratowskiClosureUp.mk T S N W Q H C P L)
      rw [KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode T,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode S,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode N,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode W,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode Q,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode H,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode C,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode P,
        KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode L]

private theorem KuratowskiClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KuratowskiClosureUp} :
    kuratowskiClosureToEventFlow x = kuratowskiClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiClosureFromEventFlow (kuratowskiClosureToEventFlow x) =
        kuratowskiClosureFromEventFlow (kuratowskiClosureToEventFlow y) :=
    congrArg kuratowskiClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KuratowskiClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KuratowskiClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem KuratowskiClosureTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : KuratowskiClosureUp, kuratowskiClosureFields x = kuratowskiClosureFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ S₁ N₁ W₁ Q₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk T₂ S₂ N₂ W₂ Q₂ H₂ C₂ P₂ L₂ =>
          injection hfields with hT tail0
          injection tail0 with hS tail1
          injection tail1 with hN tail2
          injection tail2 with hW tail3
          injection tail3 with hQ tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hL _
          subst hT
          subst hS
          subst hN
          subst hW
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hL
          rfl

instance kuratowskiClosureBHistCarrier : BHistCarrier KuratowskiClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiClosureToEventFlow
  fromEventFlow := kuratowskiClosureFromEventFlow

instance kuratowskiClosureChapterTasteGate : ChapterTasteGate KuratowskiClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiClosureFromEventFlow (kuratowskiClosureToEventFlow x) = some x
    exact KuratowskiClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KuratowskiClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kuratowskiClosureFieldFaithful : FieldFaithful KuratowskiClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kuratowskiClosureFields
  field_faithful := KuratowskiClosureTasteGate_single_carrier_alignment_field_faithful

instance kuratowskiClosureNontrivial : Nontrivial KuratowskiClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KuratowskiClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KuratowskiClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KuratowskiClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kuratowskiClosureChapterTasteGate

theorem KuratowskiClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, kuratowskiClosureDecodeBHist (kuratowskiClosureEncodeBHist h) = h) ∧
      (∀ x : KuratowskiClosureUp,
        kuratowskiClosureToEventFlow x =
          List.map kuratowskiClosureEncodeBHist (kuratowskiClosureFields x)) ∧
      (∀ x y : KuratowskiClosureUp, kuratowskiClosureFields x = kuratowskiClosureFields y →
        x = y) ∧
      (∃ x y : KuratowskiClosureUp, x ≠ y) ∧
      kuratowskiClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨KuratowskiClosureTasteGate_single_carrier_alignment_decode_encode,
      by
        intro x
        rfl,
      KuratowskiClosureTasteGate_single_carrier_alignment_field_faithful,
      ⟨KuratowskiClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        KuratowskiClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.KuratowskiClosureUp
