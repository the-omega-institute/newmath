import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardLindelofUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardLindelofUp : Type where
  | mk (I F L R Q U H C G N : BHist) : PicardLindelofUp
  deriving DecidableEq

def picardLindelofEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardLindelofEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardLindelofEncodeBHist h

def picardLindelofDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardLindelofDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardLindelofDecodeBHist tail)

private theorem PicardLindelofTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, picardLindelofDecodeBHist (picardLindelofEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardLindelofFields : PicardLindelofUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardLindelofUp.mk I F L R Q U H C G N => [I, F, L, R, Q, U, H, C, G, N]

def picardLindelofToEventFlow : PicardLindelofUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (picardLindelofFields x).map picardLindelofEncodeBHist

private def picardLindelofEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => picardLindelofEventAt index rest

def picardLindelofFromEventFlow (ef : EventFlow) : Option PicardLindelofUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardLindelofUp.mk
      (picardLindelofDecodeBHist (picardLindelofEventAt 0 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 1 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 2 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 3 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 4 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 5 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 6 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 7 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 8 ef))
      (picardLindelofDecodeBHist (picardLindelofEventAt 9 ef)))

private theorem PicardLindelofTasteGate_single_carrier_alignment_round_trip
    (x : PicardLindelofUp) :
    picardLindelofFromEventFlow (picardLindelofToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F L R Q U H C G N =>
      change
        some
          (PicardLindelofUp.mk
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist I))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist F))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist L))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist R))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist Q))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist U))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist H))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist C))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist G))
            (picardLindelofDecodeBHist (picardLindelofEncodeBHist N))) =
          some (PicardLindelofUp.mk I F L R Q U H C G N)
      rw [PicardLindelofTasteGate_single_carrier_alignment_decode I,
        PicardLindelofTasteGate_single_carrier_alignment_decode F,
        PicardLindelofTasteGate_single_carrier_alignment_decode L,
        PicardLindelofTasteGate_single_carrier_alignment_decode R,
        PicardLindelofTasteGate_single_carrier_alignment_decode Q,
        PicardLindelofTasteGate_single_carrier_alignment_decode U,
        PicardLindelofTasteGate_single_carrier_alignment_decode H,
        PicardLindelofTasteGate_single_carrier_alignment_decode C,
        PicardLindelofTasteGate_single_carrier_alignment_decode G,
        PicardLindelofTasteGate_single_carrier_alignment_decode N]

private theorem PicardLindelofTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PicardLindelofUp} :
    picardLindelofToEventFlow x = picardLindelofToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardLindelofFromEventFlow (picardLindelofToEventFlow x) =
        picardLindelofFromEventFlow (picardLindelofToEventFlow y) :=
    congrArg picardLindelofFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PicardLindelofTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PicardLindelofTasteGate_single_carrier_alignment_round_trip y)))

private theorem PicardLindelofTasteGate_single_carrier_alignment_fields :
    ∀ x y : PicardLindelofUp, picardLindelofFields x = picardLindelofFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ F₁ L₁ R₁ Q₁ U₁ H₁ C₁ G₁ N₁ =>
      cases y with
      | mk I₂ F₂ L₂ R₂ Q₂ U₂ H₂ C₂ G₂ N₂ =>
          cases hfields
          rfl

instance picardLindelofBHistCarrier : BHistCarrier PicardLindelofUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardLindelofToEventFlow
  fromEventFlow := picardLindelofFromEventFlow

instance picardLindelofChapterTasteGate : ChapterTasteGate PicardLindelofUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardLindelofFromEventFlow (picardLindelofToEventFlow x) = some x
    exact PicardLindelofTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PicardLindelofTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PicardLindelofTasteGate_single_carrier_alignment :
    (∀ h : BHist, picardLindelofDecodeBHist (picardLindelofEncodeBHist h) = h) ∧
      (∀ x : PicardLindelofUp,
        picardLindelofFromEventFlow (picardLindelofToEventFlow x) = some x) ∧
        (∀ x y : PicardLindelofUp,
          picardLindelofToEventFlow x = picardLindelofToEventFlow y → x = y) ∧
          picardLindelofEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : PicardLindelofUp,
              picardLindelofFields x = picardLindelofFields y → x = y) ∧
              (∃ x y : PicardLindelofUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PicardLindelofTasteGate_single_carrier_alignment_decode,
      PicardLindelofTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PicardLindelofTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      PicardLindelofTasteGate_single_carrier_alignment_fields,
      ⟨PicardLindelofUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        PicardLindelofUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.PicardLindelofUp
