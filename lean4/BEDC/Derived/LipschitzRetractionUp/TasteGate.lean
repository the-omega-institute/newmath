import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzRetractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzRetractionUp : Type where
  | mk (X A K G I M L E H C P N : BHist) : LipschitzRetractionUp
  deriving DecidableEq

def lipschitzRetractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzRetractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzRetractionEncodeBHist h

def lipschitzRetractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzRetractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzRetractionDecodeBHist tail)

private theorem LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzRetractionFields : LipschitzRetractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzRetractionUp.mk X A K G I M L E H C P N =>
      [X, A, K, G, I, M, L, E, H, C, P, N]

def lipschitzRetractionToEventFlow : LipschitzRetractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lipschitzRetractionFields x).map lipschitzRetractionEncodeBHist

private def lipschitzRetractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzRetractionEventAtDefault index rest

def lipschitzRetractionFromEventFlow (ef : EventFlow) : Option LipschitzRetractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzRetractionUp.mk
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 0 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 1 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 2 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 3 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 4 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 5 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 6 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 7 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 8 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 9 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 10 ef))
      (lipschitzRetractionDecodeBHist (lipschitzRetractionEventAtDefault 11 ef)))

private theorem LipschitzRetractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LipschitzRetractionUp,
      lipschitzRetractionFromEventFlow (lipschitzRetractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A K G I M L E H C P N =>
      change
        some
          (LipschitzRetractionUp.mk
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist X))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist A))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist K))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist G))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist I))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist M))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist L))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist E))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist H))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist C))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist P))
            (lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist N))) =
          some (LipschitzRetractionUp.mk X A K G I M L E H C P N)
      rw [LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode X,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode A,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode K,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode G,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode I,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode M,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode L,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode E,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode H,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode C,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode P,
        LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LipschitzRetractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LipschitzRetractionUp} :
    lipschitzRetractionToEventFlow x = lipschitzRetractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzRetractionFromEventFlow (lipschitzRetractionToEventFlow x) =
        lipschitzRetractionFromEventFlow (lipschitzRetractionToEventFlow y) :=
    congrArg lipschitzRetractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LipschitzRetractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LipschitzRetractionTasteGate_single_carrier_alignment_round_trip y)))

instance lipschitzRetractionBHistCarrier : BHistCarrier LipschitzRetractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzRetractionToEventFlow
  fromEventFlow := lipschitzRetractionFromEventFlow

instance lipschitzRetractionChapterTasteGate : ChapterTasteGate LipschitzRetractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzRetractionFromEventFlow (lipschitzRetractionToEventFlow x) = some x
    exact LipschitzRetractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LipschitzRetractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LipschitzRetractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lipschitzRetractionChapterTasteGate

theorem LipschitzRetractionTasteGate_single_carrier_alignment :
    (∀ h : BHist, lipschitzRetractionDecodeBHist (lipschitzRetractionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LipschitzRetractionUp) ∧
        Nonempty (ChapterTasteGate LipschitzRetractionUp) ∧
          lipschitzRetractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LipschitzRetractionTasteGate_single_carrier_alignment_decode_encode,
      ⟨lipschitzRetractionBHistCarrier⟩,
      ⟨lipschitzRetractionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LipschitzRetractionUp
