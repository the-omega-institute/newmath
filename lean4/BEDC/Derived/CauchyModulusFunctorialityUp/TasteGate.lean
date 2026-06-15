import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusFunctorialityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusFunctorialityUp : Type where
  | mk (S T R D W Q E H C P N : BHist) : CauchyModulusFunctorialityUp
  deriving DecidableEq

def cauchyModulusFunctorialityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusFunctorialityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusFunctorialityEncodeBHist h

def cauchyModulusFunctorialityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusFunctorialityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusFunctorialityDecodeBHist tail)

private theorem CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusFunctorialityDecodeBHist
        (cauchyModulusFunctorialityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusFunctorialityFields : CauchyModulusFunctorialityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusFunctorialityUp.mk S T R D W Q E H C P N =>
      [S, T, R, D, W, Q, E, H, C, P, N]

def cauchyModulusFunctorialityToEventFlow : CauchyModulusFunctorialityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusFunctorialityFields x).map cauchyModulusFunctorialityEncodeBHist

private def cauchyModulusFunctorialityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusFunctorialityEventAt index rest

def cauchyModulusFunctorialityFromEventFlow
    (ef : EventFlow) : Option CauchyModulusFunctorialityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusFunctorialityUp.mk
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 0 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 1 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 2 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 3 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 4 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 5 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 6 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 7 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 8 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 9 ef))
      (cauchyModulusFunctorialityDecodeBHist (cauchyModulusFunctorialityEventAt 10 ef)))

private theorem CauchyModulusFunctorialityTasteGate_single_carrier_alignment_round_trip
    (x : CauchyModulusFunctorialityUp) :
    cauchyModulusFunctorialityFromEventFlow
        (cauchyModulusFunctorialityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T R D W Q E H C P N =>
      change
        some
          (CauchyModulusFunctorialityUp.mk
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist S))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist T))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist R))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist D))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist W))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist Q))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist E))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist H))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist C))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist P))
            (cauchyModulusFunctorialityDecodeBHist
              (cauchyModulusFunctorialityEncodeBHist N))) =
          some (CauchyModulusFunctorialityUp.mk S T R D W Q E H C P N)
      rw [CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode S,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode T,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode W,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusFunctorialityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusFunctorialityUp} :
    cauchyModulusFunctorialityToEventFlow x =
        cauchyModulusFunctorialityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusFunctorialityFromEventFlow
          (cauchyModulusFunctorialityToEventFlow x) =
        cauchyModulusFunctorialityFromEventFlow
          (cauchyModulusFunctorialityToEventFlow y) :=
    congrArg cauchyModulusFunctorialityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusFunctorialityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusFunctorialityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusFunctorialityBHistCarrier :
    BHistCarrier CauchyModulusFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusFunctorialityToEventFlow
  fromEventFlow := cauchyModulusFunctorialityFromEventFlow

instance cauchyModulusFunctorialityChapterTasteGate :
    ChapterTasteGate CauchyModulusFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusFunctorialityFromEventFlow
      (cauchyModulusFunctorialityToEventFlow x) = some x
    exact CauchyModulusFunctorialityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusFunctorialityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyModulusFunctorialityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyModulusFunctorialityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusFunctorialityChapterTasteGate

theorem CauchyModulusFunctorialityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusFunctorialityDecodeBHist
        (cauchyModulusFunctorialityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyModulusFunctorialityUp) ∧
        Nonempty (ChapterTasteGate CauchyModulusFunctorialityUp) ∧
          cauchyModulusFunctorialityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyModulusFunctorialityTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchyModulusFunctorialityBHistCarrier⟩,
      ⟨cauchyModulusFunctorialityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyModulusFunctorialityUp
