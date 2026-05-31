import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBinarySearchUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBinarySearchUp : Type where
  | mk (initial test depth midpoint retained window readback bracketSeal transport replay
      provenance localName : BHist) : DyadicBinarySearchUp

def dyadicBinarySearchEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBinarySearchEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBinarySearchEncodeBHist h

def dyadicBinarySearchDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBinarySearchDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBinarySearchDecodeBHist tail)

private theorem DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicBinarySearchFields : DyadicBinarySearchUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBinarySearchUp.mk initial test depth midpoint retained window readback bracketSeal
      transport replay provenance localName =>
      [initial, test, depth, midpoint, retained, window, readback, bracketSeal, transport, replay,
        provenance, localName]

def dyadicBinarySearchToEventFlow : DyadicBinarySearchUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicBinarySearchFields x).map dyadicBinarySearchEncodeBHist

private def dyadicBinarySearchEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicBinarySearchEventAtDefault index rest

def dyadicBinarySearchFromEventFlow (ef : EventFlow) : Option DyadicBinarySearchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicBinarySearchUp.mk
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 0 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 1 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 2 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 3 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 4 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 5 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 6 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 7 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 8 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 9 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 10 ef))
      (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEventAtDefault 11 ef)))

private theorem DyadicBinarySearchTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicBinarySearchUp,
      dyadicBinarySearchFromEventFlow (dyadicBinarySearchToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk initial test depth midpoint retained window readback bracketSeal transport replay provenance
      localName =>
      change
        some
          (DyadicBinarySearchUp.mk
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist initial))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist test))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist depth))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist midpoint))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist retained))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist window))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist readback))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist bracketSeal))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist transport))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist replay))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist provenance))
            (dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist localName))) =
          some
            (DyadicBinarySearchUp.mk initial test depth midpoint retained window readback bracketSeal
              transport replay provenance localName)
      rw [DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode initial,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode test,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode depth,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode midpoint,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode retained,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode window,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode readback,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode bracketSeal,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode transport,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode replay,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode provenance,
        DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode localName]

private theorem DyadicBinarySearchTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicBinarySearchUp} :
    dyadicBinarySearchToEventFlow x = dyadicBinarySearchToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBinarySearchFromEventFlow (dyadicBinarySearchToEventFlow x) =
        dyadicBinarySearchFromEventFlow (dyadicBinarySearchToEventFlow y) :=
    congrArg dyadicBinarySearchFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicBinarySearchTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicBinarySearchTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicBinarySearchBHistCarrier : BHistCarrier DyadicBinarySearchUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBinarySearchToEventFlow
  fromEventFlow := dyadicBinarySearchFromEventFlow

instance dyadicBinarySearchChapterTasteGate : ChapterTasteGate DyadicBinarySearchUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicBinarySearchFromEventFlow (dyadicBinarySearchToEventFlow x) = some x
    exact DyadicBinarySearchTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicBinarySearchTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicBinarySearchUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicBinarySearchChapterTasteGate

theorem DyadicBinarySearchTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicBinarySearchUp) ∧
      (∀ h : BHist, dyadicBinarySearchDecodeBHist (dyadicBinarySearchEncodeBHist h) = h) ∧
        (∀ x : DyadicBinarySearchUp,
          dyadicBinarySearchFromEventFlow (dyadicBinarySearchToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨dyadicBinarySearchChapterTasteGate⟩,
      DyadicBinarySearchTasteGate_single_carrier_alignment_decode_encode,
      DyadicBinarySearchTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.DyadicBinarySearchUp
