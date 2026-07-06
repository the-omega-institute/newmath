import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFiniteIntervalChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFiniteIntervalChainUp : Type where
  | mk (E A R M I H C P N : BHist) : BishopFiniteIntervalChainUp
  deriving DecidableEq

def bishopFiniteIntervalChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFiniteIntervalChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFiniteIntervalChainEncodeBHist h

def bishopFiniteIntervalChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFiniteIntervalChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFiniteIntervalChainDecodeBHist tail)

private theorem BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopFiniteIntervalChainFields : BishopFiniteIntervalChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFiniteIntervalChainUp.mk E A R M I H C P N => [E, A, R, M, I, H, C, P, N]

def bishopFiniteIntervalChainToEventFlow : BishopFiniteIntervalChainUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopFiniteIntervalChainFields x).map bishopFiniteIntervalChainEncodeBHist

private def bishopFiniteIntervalChainEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopFiniteIntervalChainEventAtDefault index rest

def bishopFiniteIntervalChainFromEventFlow (ef : EventFlow) : Option BishopFiniteIntervalChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopFiniteIntervalChainUp.mk
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 0 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 1 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 2 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 3 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 4 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 5 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 6 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 7 ef))
      (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEventAtDefault 8 ef)))

private theorem BishopFiniteIntervalChainTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopFiniteIntervalChainUp,
      bishopFiniteIntervalChainFromEventFlow (bishopFiniteIntervalChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E A R M I H C P N =>
      change
        some
          (BishopFiniteIntervalChainUp.mk
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist E))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist A))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist R))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist M))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist I))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist H))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist C))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist P))
            (bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist N))) =
          some (BishopFiniteIntervalChainUp.mk E A R M I H C P N)
      rw [BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode E,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode A,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode R,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode M,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode I,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode H,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode C,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode P,
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode N]

private theorem BishopFiniteIntervalChainTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopFiniteIntervalChainUp} :
    bishopFiniteIntervalChainToEventFlow x = bishopFiniteIntervalChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFiniteIntervalChainFromEventFlow (bishopFiniteIntervalChainToEventFlow x) =
        bishopFiniteIntervalChainFromEventFlow (bishopFiniteIntervalChainToEventFlow y) :=
    congrArg bishopFiniteIntervalChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopFiniteIntervalChainTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopFiniteIntervalChainTasteGate_single_carrier_alignment_round_trip y)))

instance bishopFiniteIntervalChainBHistCarrier : BHistCarrier BishopFiniteIntervalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFiniteIntervalChainToEventFlow
  fromEventFlow := bishopFiniteIntervalChainFromEventFlow

instance bishopFiniteIntervalChainChapterTasteGate :
    ChapterTasteGate BishopFiniteIntervalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopFiniteIntervalChainFromEventFlow (bishopFiniteIntervalChainToEventFlow x) = some x
    exact BishopFiniteIntervalChainTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopFiniteIntervalChainTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopFiniteIntervalChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFiniteIntervalChainChapterTasteGate

theorem BishopFiniteIntervalChainTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bishopFiniteIntervalChainDecodeBHist (bishopFiniteIntervalChainEncodeBHist h) = h) ∧
    (forall x : BishopFiniteIntervalChainUp,
      bishopFiniteIntervalChainFromEventFlow (bishopFiniteIntervalChainToEventFlow x) = some x) ∧
    (forall x y : BishopFiniteIntervalChainUp,
      bishopFiniteIntervalChainToEventFlow x = bishopFiniteIntervalChainToEventFlow y -> x = y) ∧
    bishopFiniteIntervalChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopFiniteIntervalChainTasteGate_single_carrier_alignment_decode,
      BishopFiniteIntervalChainTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        BishopFiniteIntervalChainTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BishopFiniteIntervalChainUp
