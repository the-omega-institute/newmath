import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRealIntervalChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRealIntervalChainUp : Type where
  | mk (E I J D S R L H C P N : BHist) : FiniteRealIntervalChainUp
  deriving DecidableEq

def finiteRealIntervalChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRealIntervalChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRealIntervalChainEncodeBHist h

def finiteRealIntervalChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRealIntervalChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRealIntervalChainDecodeBHist tail)

private theorem finiteRealIntervalChain_decode_encode_bhist :
    ∀ h : BHist,
      finiteRealIntervalChainDecodeBHist
        (finiteRealIntervalChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRealIntervalChainFields : FiniteRealIntervalChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealIntervalChainUp.mk E I J D S R L H C P N =>
      [E, I, J, D, S, R, L, H, C, P, N]

def finiteRealIntervalChainToEventFlow : FiniteRealIntervalChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteRealIntervalChainFields x).map finiteRealIntervalChainEncodeBHist

private def finiteRealIntervalChainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRealIntervalChainEventAt index rest

def finiteRealIntervalChainFromEventFlow
    (ef : EventFlow) : Option FiniteRealIntervalChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRealIntervalChainUp.mk
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 0 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 1 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 2 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 3 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 4 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 5 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 6 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 7 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 8 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 9 ef))
      (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEventAt 10 ef)))

private theorem finiteRealIntervalChain_round_trip (x : FiniteRealIntervalChainUp) :
    finiteRealIntervalChainFromEventFlow (finiteRealIntervalChainToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E I J D S R L H C P N =>
      change
        some
          (FiniteRealIntervalChainUp.mk
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist E))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist I))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist J))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist D))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist S))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist R))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist L))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist H))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist C))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist P))
            (finiteRealIntervalChainDecodeBHist (finiteRealIntervalChainEncodeBHist N))) =
          some (FiniteRealIntervalChainUp.mk E I J D S R L H C P N)
      rw [finiteRealIntervalChain_decode_encode_bhist E,
        finiteRealIntervalChain_decode_encode_bhist I,
        finiteRealIntervalChain_decode_encode_bhist J,
        finiteRealIntervalChain_decode_encode_bhist D,
        finiteRealIntervalChain_decode_encode_bhist S,
        finiteRealIntervalChain_decode_encode_bhist R,
        finiteRealIntervalChain_decode_encode_bhist L,
        finiteRealIntervalChain_decode_encode_bhist H,
        finiteRealIntervalChain_decode_encode_bhist C,
        finiteRealIntervalChain_decode_encode_bhist P,
        finiteRealIntervalChain_decode_encode_bhist N]

private theorem finiteRealIntervalChainToEventFlow_injective
    {x y : FiniteRealIntervalChainUp} :
    finiteRealIntervalChainToEventFlow x = finiteRealIntervalChainToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRealIntervalChainFromEventFlow (finiteRealIntervalChainToEventFlow x) =
        finiteRealIntervalChainFromEventFlow (finiteRealIntervalChainToEventFlow y) :=
    congrArg finiteRealIntervalChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteRealIntervalChain_round_trip x).symm
      (Eq.trans hread (finiteRealIntervalChain_round_trip y)))

private theorem finiteRealIntervalChain_fields_faithful :
    ∀ x y : FiniteRealIntervalChainUp,
      finiteRealIntervalChainFields x = finiteRealIntervalChainFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E I J D S R L H C P N =>
      cases y with
      | mk E' I' J' D' S' R' L' H' C' P' N' =>
          cases hfields
          rfl

instance finiteRealIntervalChainBHistCarrier :
    BHistCarrier FiniteRealIntervalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRealIntervalChainToEventFlow
  fromEventFlow := finiteRealIntervalChainFromEventFlow

instance finiteRealIntervalChainChapterTasteGate :
    ChapterTasteGate FiniteRealIntervalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteRealIntervalChainFromEventFlow (finiteRealIntervalChainToEventFlow x) =
        some x
    exact finiteRealIntervalChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteRealIntervalChainToEventFlow_injective heq)

instance finiteRealIntervalChainFieldFaithful :
    FieldFaithful FiniteRealIntervalChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRealIntervalChainFields
  field_faithful := finiteRealIntervalChain_fields_faithful

instance finiteRealIntervalChainNontrivial :
    Nontrivial FiniteRealIntervalChainUp where
  witness_pair :=
    ⟨FiniteRealIntervalChainUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteRealIntervalChainUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem FiniteRealIntervalChainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteRealIntervalChainDecodeBHist
          (finiteRealIntervalChainEncodeBHist h) = h) ∧
      (∀ x : FiniteRealIntervalChainUp,
        finiteRealIntervalChainFromEventFlow
          (finiteRealIntervalChainToEventFlow x) = some x) ∧
      (∀ x y : FiniteRealIntervalChainUp,
        finiteRealIntervalChainToEventFlow x =
          finiteRealIntervalChainToEventFlow y → x = y) ∧
      finiteRealIntervalChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨finiteRealIntervalChain_decode_encode_bhist,
    finiteRealIntervalChain_round_trip,
    fun _ _ heq => finiteRealIntervalChainToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.FiniteRealIntervalChainUp
