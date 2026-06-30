import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoetherSymmetryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoetherSymmetryUp : Type where
  | mk (L E J H C P S : BHist) : NoetherSymmetryUp
  deriving DecidableEq

def noetherSymmetryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noetherSymmetryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noetherSymmetryEncodeBHist h

def noetherSymmetryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noetherSymmetryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noetherSymmetryDecodeBHist tail)

private theorem NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def noetherSymmetryFields : NoetherSymmetryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NoetherSymmetryUp.mk L E J H C P S => [L, E, J, H, C, P, S]

def noetherSymmetryToEventFlow : NoetherSymmetryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (noetherSymmetryFields x).map noetherSymmetryEncodeBHist

private def NoetherSymmetryTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      NoetherSymmetryTasteGate_single_carrier_alignment_eventAt index rest

def noetherSymmetryFromEventFlow (ef : EventFlow) : Option NoetherSymmetryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NoetherSymmetryUp.mk
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 0 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 1 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 2 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 3 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 4 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 5 ef))
      (noetherSymmetryDecodeBHist
        (NoetherSymmetryTasteGate_single_carrier_alignment_eventAt 6 ef)))

private theorem NoetherSymmetryTasteGate_single_carrier_alignment_round_trip
    (x : NoetherSymmetryUp) :
    noetherSymmetryFromEventFlow (noetherSymmetryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L E J H C P S =>
      change
        some
          (NoetherSymmetryUp.mk
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist L))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist E))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist J))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist H))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist C))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist P))
            (noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist S))) =
          some (NoetherSymmetryUp.mk L E J H C P S)
      rw [NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode L,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode E,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode J,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode H,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode C,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode P,
        NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode S]

private theorem NoetherSymmetryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NoetherSymmetryUp} :
    noetherSymmetryToEventFlow x = noetherSymmetryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noetherSymmetryFromEventFlow (noetherSymmetryToEventFlow x) =
        noetherSymmetryFromEventFlow (noetherSymmetryToEventFlow y) :=
    congrArg noetherSymmetryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NoetherSymmetryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NoetherSymmetryTasteGate_single_carrier_alignment_round_trip y)))

instance noetherSymmetryBHistCarrier : BHistCarrier NoetherSymmetryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noetherSymmetryToEventFlow
  fromEventFlow := noetherSymmetryFromEventFlow

instance noetherSymmetryChapterTasteGate : ChapterTasteGate NoetherSymmetryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noetherSymmetryFromEventFlow (noetherSymmetryToEventFlow x) = some x
    exact NoetherSymmetryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NoetherSymmetryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NoetherSymmetryTasteGate_single_carrier_alignment :
    (forall h : BHist, noetherSymmetryDecodeBHist (noetherSymmetryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NoetherSymmetryUp) ∧
        Nonempty (ChapterTasteGate NoetherSymmetryUp) ∧
          noetherSymmetryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NoetherSymmetryTasteGate_single_carrier_alignment_decode_encode,
      ⟨noetherSymmetryBHistCarrier⟩,
      ⟨noetherSymmetryChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NoetherSymmetryUp
