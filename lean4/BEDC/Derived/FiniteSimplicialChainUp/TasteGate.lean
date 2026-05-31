import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSimplicialChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSimplicialChainUp : Type where
  | mk
      (simplicial finset abgroup grading boundary cancellation transport replay provenance name :
        BHist) :
      FiniteSimplicialChainUp
  deriving DecidableEq

def finiteSimplicialChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSimplicialChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSimplicialChainEncodeBHist h

def finiteSimplicialChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSimplicialChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSimplicialChainDecodeBHist tail)

private theorem finiteSimplicialChain_decode_encode_bhist :
    ∀ h : BHist,
      finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSimplicialChainFields : FiniteSimplicialChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSimplicialChainUp.mk simplicial finset abgroup grading boundary cancellation transport
      replay provenance name =>
      [simplicial, finset, abgroup, grading, boundary, cancellation, transport, replay,
        provenance, name]

def finiteSimplicialChainToEventFlow : FiniteSimplicialChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSimplicialChainFields x).map finiteSimplicialChainEncodeBHist

private def finiteSimplicialChainEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteSimplicialChainEventAt index rest

def finiteSimplicialChainFromEventFlow
    (flow : EventFlow) : Option FiniteSimplicialChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSimplicialChainUp.mk
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 0 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 1 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 2 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 3 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 4 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 5 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 6 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 7 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 8 flow))
      (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEventAt 9 flow)))

private theorem finiteSimplicialChain_round_trip :
    ∀ x : FiniteSimplicialChainUp,
      finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk simplicial finset abgroup grading boundary cancellation transport replay provenance name =>
      change
        some
          (FiniteSimplicialChainUp.mk
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist simplicial))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist finset))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist abgroup))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist grading))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist boundary))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist cancellation))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist transport))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist replay))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist provenance))
            (finiteSimplicialChainDecodeBHist (finiteSimplicialChainEncodeBHist name))) =
          some
            (FiniteSimplicialChainUp.mk simplicial finset abgroup grading boundary
              cancellation transport replay provenance name)
      rw [finiteSimplicialChain_decode_encode_bhist simplicial,
        finiteSimplicialChain_decode_encode_bhist finset,
        finiteSimplicialChain_decode_encode_bhist abgroup,
        finiteSimplicialChain_decode_encode_bhist grading,
        finiteSimplicialChain_decode_encode_bhist boundary,
        finiteSimplicialChain_decode_encode_bhist cancellation,
        finiteSimplicialChain_decode_encode_bhist transport,
        finiteSimplicialChain_decode_encode_bhist replay,
        finiteSimplicialChain_decode_encode_bhist provenance,
        finiteSimplicialChain_decode_encode_bhist name]

private theorem finiteSimplicialChainToEventFlow_injective
    {x y : FiniteSimplicialChainUp} :
    finiteSimplicialChainToEventFlow x = finiteSimplicialChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) =
        finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow y) :=
    congrArg finiteSimplicialChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteSimplicialChain_round_trip x).symm
      (Eq.trans hread (finiteSimplicialChain_round_trip y)))

instance finiteSimplicialChainBHistCarrier :
    BHistCarrier FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSimplicialChainToEventFlow
  fromEventFlow := finiteSimplicialChainFromEventFlow

instance finiteSimplicialChainChapterTasteGate :
    ChapterTasteGate FiniteSimplicialChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSimplicialChainFromEventFlow (finiteSimplicialChainToEventFlow x) = some x
    exact finiteSimplicialChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteSimplicialChainToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteSimplicialChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteSimplicialChainChapterTasteGate

theorem FiniteSimplicialChainTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier FiniteSimplicialChainUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate FiniteSimplicialChainUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨finiteSimplicialChainBHistCarrier⟩
  · exact ⟨finiteSimplicialChainChapterTasteGate⟩

end BEDC.Derived.FiniteSimplicialChainUp
