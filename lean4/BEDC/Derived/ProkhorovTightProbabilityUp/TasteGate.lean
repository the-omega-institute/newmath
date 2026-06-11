import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProkhorovTightProbabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProkhorovTightProbabilityUp : Type where
  | mk (P D M K N E R T H C Q L : BHist) : ProkhorovTightProbabilityUp
  deriving DecidableEq

def prokhorovTightProbabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: prokhorovTightProbabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: prokhorovTightProbabilityEncodeBHist h

def prokhorovTightProbabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (prokhorovTightProbabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (prokhorovTightProbabilityDecodeBHist tail)

private theorem ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      prokhorovTightProbabilityDecodeBHist
        (prokhorovTightProbabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def prokhorovTightProbabilityToEventFlow : ProkhorovTightProbabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ProkhorovTightProbabilityUp.mk P D M K N E R T H C Q L =>
      [[BMark.b0],
        prokhorovTightProbabilityEncodeBHist P,
        [BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        prokhorovTightProbabilityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prokhorovTightProbabilityEncodeBHist L]

private def prokhorovTightProbabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => prokhorovTightProbabilityEventAtDefault index rest

def prokhorovTightProbabilityFromEventFlow
    (ef : EventFlow) : Option ProkhorovTightProbabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProkhorovTightProbabilityUp.mk
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 1 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 3 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 5 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 7 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 9 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 11 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 13 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 15 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 17 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 19 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 21 ef))
      (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEventAtDefault 23 ef)))

private theorem ProkhorovTightProbabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProkhorovTightProbabilityUp,
      prokhorovTightProbabilityFromEventFlow
        (prokhorovTightProbabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P D M K N E R T H C Q L =>
      change
        some
          (ProkhorovTightProbabilityUp.mk
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist P))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist D))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist M))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist K))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist N))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist E))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist R))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist T))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist H))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist C))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist Q))
            (prokhorovTightProbabilityDecodeBHist (prokhorovTightProbabilityEncodeBHist L))) =
          some (ProkhorovTightProbabilityUp.mk P D M K N E R T H C Q L)
      rw [ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode P,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode D,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode M,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode K,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode N,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode E,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode R,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode T,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode H,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode C,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode Q,
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode L]

private theorem ProkhorovTightProbabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProkhorovTightProbabilityUp} :
    prokhorovTightProbabilityToEventFlow x =
      prokhorovTightProbabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      prokhorovTightProbabilityFromEventFlow (prokhorovTightProbabilityToEventFlow x) =
        prokhorovTightProbabilityFromEventFlow (prokhorovTightProbabilityToEventFlow y) :=
    congrArg prokhorovTightProbabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProkhorovTightProbabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ProkhorovTightProbabilityTasteGate_single_carrier_alignment_round_trip y)))

instance prokhorovTightProbabilityBHistCarrier :
    BHistCarrier ProkhorovTightProbabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := prokhorovTightProbabilityToEventFlow
  fromEventFlow := prokhorovTightProbabilityFromEventFlow

instance prokhorovTightProbabilityChapterTasteGate :
    ChapterTasteGate ProkhorovTightProbabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      prokhorovTightProbabilityFromEventFlow
        (prokhorovTightProbabilityToEventFlow x) = some x
    exact ProkhorovTightProbabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ProkhorovTightProbabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance prokhorovTightProbabilityNontrivial :
    Nontrivial ProkhorovTightProbabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProkhorovTightProbabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ProkhorovTightProbabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProkhorovTightProbabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  prokhorovTightProbabilityChapterTasteGate

theorem ProkhorovTightProbabilityTasteGate_single_carrier_alignment :
    ChapterTasteGate ProkhorovTightProbabilityUp ∧
      (∀ h : BHist,
        prokhorovTightProbabilityDecodeBHist
          (prokhorovTightProbabilityEncodeBHist h) = h) ∧
        (∀ x : ProkhorovTightProbabilityUp,
          prokhorovTightProbabilityFromEventFlow
            (prokhorovTightProbabilityToEventFlow x) = some x) ∧
          (∀ x y : ProkhorovTightProbabilityUp,
            prokhorovTightProbabilityToEventFlow x =
              prokhorovTightProbabilityToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨prokhorovTightProbabilityChapterTasteGate,
      ProkhorovTightProbabilityTasteGate_single_carrier_alignment_decode_encode,
      ProkhorovTightProbabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ProkhorovTightProbabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)⟩

end BEDC.Derived.ProkhorovTightProbabilityUp
