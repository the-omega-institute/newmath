import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GreedySpectralClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GreedySpectralClosureUp : Type where
  | packet
      (support anchor median terminal radius layered transport replay provenance
        localName : BHist) :
      GreedySpectralClosureUp
  deriving DecidableEq

def greedySpectralClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: greedySpectralClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: greedySpectralClosureEncodeBHist h

def greedySpectralClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (greedySpectralClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (greedySpectralClosureDecodeBHist tail)

private theorem greedySpectralClosureDecodeEncode :
    ∀ h : BHist, greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def greedySpectralClosureFields : GreedySpectralClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GreedySpectralClosureUp.packet support anchor median terminal radius layered transport
      replay provenance localName =>
      [support, anchor, median, terminal, radius, layered, transport, replay, provenance,
        localName]

def greedySpectralClosureToEventFlow : GreedySpectralClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (greedySpectralClosureFields x).map greedySpectralClosureEncodeBHist

private def greedySpectralClosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => greedySpectralClosureEventAt index rest

def greedySpectralClosureFromEventFlow (ef : EventFlow) : Option GreedySpectralClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GreedySpectralClosureUp.packet
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 0 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 1 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 2 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 3 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 4 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 5 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 6 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 7 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 8 ef))
      (greedySpectralClosureDecodeBHist (greedySpectralClosureEventAt 9 ef)))

private theorem greedySpectralClosure_round_trip (x : GreedySpectralClosureUp) :
    greedySpectralClosureFromEventFlow (greedySpectralClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet support anchor median terminal radius layered transport replay provenance localName =>
      change
        some
          (GreedySpectralClosureUp.packet
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist support))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist anchor))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist median))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist terminal))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist radius))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist layered))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist transport))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist replay))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist provenance))
            (greedySpectralClosureDecodeBHist (greedySpectralClosureEncodeBHist localName))) =
          some
            (GreedySpectralClosureUp.packet support anchor median terminal radius layered
              transport replay provenance localName)
      rw [greedySpectralClosureDecodeEncode support, greedySpectralClosureDecodeEncode anchor,
        greedySpectralClosureDecodeEncode median, greedySpectralClosureDecodeEncode terminal,
        greedySpectralClosureDecodeEncode radius, greedySpectralClosureDecodeEncode layered,
        greedySpectralClosureDecodeEncode transport, greedySpectralClosureDecodeEncode replay,
        greedySpectralClosureDecodeEncode provenance, greedySpectralClosureDecodeEncode localName]

private theorem greedySpectralClosureToEventFlow_injective {x y : GreedySpectralClosureUp} :
    greedySpectralClosureToEventFlow x = greedySpectralClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      greedySpectralClosureFromEventFlow (greedySpectralClosureToEventFlow x) =
        greedySpectralClosureFromEventFlow (greedySpectralClosureToEventFlow y) :=
    congrArg greedySpectralClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (greedySpectralClosure_round_trip x).symm
      (Eq.trans hread (greedySpectralClosure_round_trip y)))

private theorem greedySpectralClosureFieldFaithfulProof :
    ∀ x y : GreedySpectralClosureUp,
      greedySpectralClosureFields x = greedySpectralClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet support1 anchor1 median1 terminal1 radius1 layered1 transport1 replay1 provenance1
      localName1 =>
      cases y with
      | packet support2 anchor2 median2 terminal2 radius2 layered2 transport2 replay2 provenance2
          localName2 =>
          cases hfields
          rfl

instance greedySpectralClosureBHistCarrier : BHistCarrier GreedySpectralClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := greedySpectralClosureToEventFlow
  fromEventFlow := greedySpectralClosureFromEventFlow

instance greedySpectralClosureChapterTasteGate :
    ChapterTasteGate GreedySpectralClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change greedySpectralClosureFromEventFlow (greedySpectralClosureToEventFlow x) = some x
    exact greedySpectralClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (greedySpectralClosureToEventFlow_injective heq)

instance greedySpectralClosureFieldFaithful : FieldFaithful GreedySpectralClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := greedySpectralClosureFields
  field_faithful := greedySpectralClosureFieldFaithfulProof

instance greedySpectralClosureNontrivial : Nontrivial GreedySpectralClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GreedySpectralClosureUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GreedySpectralClosureUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GreedySpectralClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  greedySpectralClosureChapterTasteGate

def taste_gate_witness : FieldFaithful GreedySpectralClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  greedySpectralClosureFieldFaithful

theorem GreedySpectralClosureUpTasteGate_single_carrier_alignment :
    (∀ x : GreedySpectralClosureUp,
      greedySpectralClosureFromEventFlow (greedySpectralClosureToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier GreedySpectralClosureUp) ∧
        Nonempty (ChapterTasteGate GreedySpectralClosureUp) ∧
          Nonempty (FieldFaithful GreedySpectralClosureUp) ∧
            greedySpectralClosureFields
                (GreedySpectralClosureUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨greedySpectralClosure_round_trip,
      ⟨greedySpectralClosureBHistCarrier⟩,
      ⟨greedySpectralClosureChapterTasteGate⟩,
      ⟨greedySpectralClosureFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.GreedySpectralClosureUp
