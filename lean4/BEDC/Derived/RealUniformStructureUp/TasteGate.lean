import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformStructureUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformStructureUp : Type where
  | mk
      (real metric uniform cauchyFilter dyadic stream regSeq transport replay provenance
        localNameCert : BHist) :
        RealUniformStructureUp
  deriving DecidableEq

def realUniformStructureEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformStructureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformStructureEncodeBHist h

def realUniformStructureDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformStructureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformStructureDecodeBHist tail)

private theorem RealUniformStructureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realUniformStructureDecodeBHist (realUniformStructureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformStructureFields : RealUniformStructureUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformStructureUp.mk real metric uniform cauchyFilter dyadic stream regSeq transport
      replay provenance localNameCert =>
      [real, metric, uniform, cauchyFilter, dyadic, stream, regSeq, transport, replay,
        provenance, localNameCert]

def realUniformStructureToEventFlow : RealUniformStructureUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realUniformStructureFields x).map realUniformStructureEncodeBHist

private def realUniformStructureEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformStructureEventAt index rest

def realUniformStructureFromEventFlow : EventFlow -> Option RealUniformStructureUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealUniformStructureUp.mk
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 0 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 1 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 2 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 3 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 4 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 5 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 6 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 7 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 8 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 9 ef))
          (realUniformStructureDecodeBHist (realUniformStructureEventAt 10 ef)))

private theorem RealUniformStructureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformStructureUp,
      realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk real metric uniform cauchyFilter dyadic stream regSeq transport replay provenance
      localNameCert =>
      change
        some
          (RealUniformStructureUp.mk
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist real))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist metric))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist uniform))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist cauchyFilter))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist dyadic))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist stream))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist regSeq))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist transport))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist replay))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist provenance))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist localNameCert))) =
          some
            (RealUniformStructureUp.mk real metric uniform cauchyFilter dyadic stream regSeq
              transport replay provenance localNameCert)
      rw [RealUniformStructureTasteGate_single_carrier_alignment_decode_encode real,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode metric,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode uniform,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode cauchyFilter,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode dyadic,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode stream,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode regSeq,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode transport,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode replay,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode provenance,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformStructureUp} :
    realUniformStructureToEventFlow x = realUniformStructureToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) =
        realUniformStructureFromEventFlow (realUniformStructureToEventFlow y) :=
    congrArg realUniformStructureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealUniformStructureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealUniformStructureTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealUniformStructureTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealUniformStructureUp, realUniformStructureFields x = realUniformStructureFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk real₁ metric₁ uniform₁ cauchyFilter₁ dyadic₁ stream₁ regSeq₁ transport₁ replay₁
      provenance₁ localNameCert₁ =>
      cases y with
      | mk real₂ metric₂ uniform₂ cauchyFilter₂ dyadic₂ stream₂ regSeq₂ transport₂ replay₂
          provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance realUniformStructureBHistCarrier : BHistCarrier RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformStructureToEventFlow
  fromEventFlow := realUniformStructureFromEventFlow

instance realUniformStructureChapterTasteGate : ChapterTasteGate RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x
    exact RealUniformStructureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realUniformStructureFieldFaithful : FieldFaithful RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformStructureFields
  field_faithful := by
    intro x y h
    change realUniformStructureFields x = realUniformStructureFields y at h
    exact RealUniformStructureTasteGate_single_carrier_alignment_field_faithful x y h

instance realUniformStructureNontrivial : Nontrivial RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformStructureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformStructureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealUniformStructureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealUniformStructureUp) ∧
      Nonempty (FieldFaithful RealUniformStructureUp) ∧
        Nonempty (Nontrivial RealUniformStructureUp) ∧
          (∀ h : BHist,
            realUniformStructureDecodeBHist (realUniformStructureEncodeBHist h) = h) ∧
            (∀ x : RealUniformStructureUp,
              realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x) ∧
              (∀ x y : RealUniformStructureUp,
                realUniformStructureToEventFlow x = realUniformStructureToEventFlow y -> x = y) ∧
                realUniformStructureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨realUniformStructureChapterTasteGate⟩
  · constructor
    · exact ⟨realUniformStructureFieldFaithful⟩
    · constructor
      · exact ⟨realUniformStructureNontrivial⟩
      · constructor
        · exact RealUniformStructureTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact RealUniformStructureTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RealUniformStructureUp.TasteGate
