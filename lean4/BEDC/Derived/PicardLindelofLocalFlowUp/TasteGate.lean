import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardLindelofLocalFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardLindelofLocalFlowUp : Type where
  | mk (O F K L M S R H C G N : BHist) : PicardLindelofLocalFlowUp
  deriving DecidableEq

def picardLindelofLocalFlowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardLindelofLocalFlowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardLindelofLocalFlowEncodeBHist h

def picardLindelofLocalFlowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardLindelofLocalFlowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardLindelofLocalFlowDecodeBHist tail)

private theorem PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardLindelofLocalFlowFields : PicardLindelofLocalFlowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardLindelofLocalFlowUp.mk O F K L M S R H C G N => [O, F, K, L, M, S, R, H, C, G, N]

def picardLindelofLocalFlowToEventFlow : PicardLindelofLocalFlowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (picardLindelofLocalFlowFields x).map picardLindelofLocalFlowEncodeBHist

private def picardLindelofLocalFlowEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => picardLindelofLocalFlowEventAt index rest

def picardLindelofLocalFlowFromEventFlow (ef : EventFlow) :
    Option PicardLindelofLocalFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardLindelofLocalFlowUp.mk
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 0 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 1 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 2 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 3 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 4 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 5 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 6 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 7 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 8 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 9 ef))
      (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEventAt 10 ef)))

private theorem PicardLindelofLocalFlowTasteGate_single_carrier_alignment_round_trip
    (x : PicardLindelofLocalFlowUp) :
    picardLindelofLocalFlowFromEventFlow (picardLindelofLocalFlowToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O F K L M S R H C G N =>
      change
        some
          (PicardLindelofLocalFlowUp.mk
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist O))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist F))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist K))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist L))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist M))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist S))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist R))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist H))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist C))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist G))
            (picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist N))) =
          some (PicardLindelofLocalFlowUp.mk O F K L M S R H C G N)
      rw [PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode O,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode F,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode K,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode L,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode M,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode S,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode R,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode H,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode C,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode G,
        PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode N]

private theorem picardLindelofLocalFlowToEventFlow_injective
    {x y : PicardLindelofLocalFlowUp} :
    picardLindelofLocalFlowToEventFlow x = picardLindelofLocalFlowToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardLindelofLocalFlowFromEventFlow (picardLindelofLocalFlowToEventFlow x) =
        picardLindelofLocalFlowFromEventFlow (picardLindelofLocalFlowToEventFlow y) :=
    congrArg picardLindelofLocalFlowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PicardLindelofLocalFlowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PicardLindelofLocalFlowTasteGate_single_carrier_alignment_round_trip y)))

private theorem PicardLindelofLocalFlowTasteGate_single_carrier_alignment_fields :
    ∀ x y : PicardLindelofLocalFlowUp,
      picardLindelofLocalFlowFields x = picardLindelofLocalFlowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ F₁ K₁ L₁ M₁ S₁ R₁ H₁ C₁ G₁ N₁ =>
      cases y with
      | mk O₂ F₂ K₂ L₂ M₂ S₂ R₂ H₂ C₂ G₂ N₂ =>
          cases hfields
          rfl

instance picardLindelofLocalFlowBHistCarrier :
    BHistCarrier PicardLindelofLocalFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardLindelofLocalFlowToEventFlow
  fromEventFlow := picardLindelofLocalFlowFromEventFlow

instance picardLindelofLocalFlowChapterTasteGate :
    ChapterTasteGate PicardLindelofLocalFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardLindelofLocalFlowFromEventFlow (picardLindelofLocalFlowToEventFlow x) =
      some x
    exact PicardLindelofLocalFlowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (picardLindelofLocalFlowToEventFlow_injective heq)

theorem PicardLindelofLocalFlowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        picardLindelofLocalFlowDecodeBHist (picardLindelofLocalFlowEncodeBHist h) = h) ∧
      (∀ x : PicardLindelofLocalFlowUp,
        picardLindelofLocalFlowFromEventFlow (picardLindelofLocalFlowToEventFlow x) =
          some x) ∧
        (∀ x y : PicardLindelofLocalFlowUp,
          picardLindelofLocalFlowToEventFlow x = picardLindelofLocalFlowToEventFlow y ->
            x = y) ∧
          picardLindelofLocalFlowEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : PicardLindelofLocalFlowUp,
              picardLindelofLocalFlowFields x = picardLindelofLocalFlowFields y ->
                x = y) ∧
              (∃ x y : PicardLindelofLocalFlowUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PicardLindelofLocalFlowTasteGate_single_carrier_alignment_decode,
      PicardLindelofLocalFlowTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => picardLindelofLocalFlowToEventFlow_injective heq),
      rfl,
      PicardLindelofLocalFlowTasteGate_single_carrier_alignment_fields,
      ⟨PicardLindelofLocalFlowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        PicardLindelofLocalFlowUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.PicardLindelofLocalFlowUp
