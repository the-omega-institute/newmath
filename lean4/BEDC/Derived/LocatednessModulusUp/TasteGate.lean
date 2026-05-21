import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatednessModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatednessModulusUp : Type where
  | mk
      (tolerance locatedInterval rationalCells dyadic stream regSeq realSeal transport
        continuation provenance localNameCert : BHist) :
        LocatednessModulusUp
  deriving DecidableEq

def locatednessModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatednessModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatednessModulusEncodeBHist h

def locatednessModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatednessModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatednessModulusDecodeBHist tail)

private theorem LocatednessModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatednessModulusDecodeBHist (locatednessModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatednessModulusFields : LocatednessModulusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatednessModulusUp.mk tolerance locatedInterval rationalCells dyadic stream regSeq realSeal
      transport continuation provenance localNameCert =>
      [tolerance, locatedInterval, rationalCells, dyadic, stream, regSeq, realSeal, transport,
        continuation, provenance, localNameCert]

def locatednessModulusToEventFlow : LocatednessModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatednessModulusFields x).map locatednessModulusEncodeBHist

private def locatednessModulusEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatednessModulusEventAt index rest

def locatednessModulusFromEventFlow : EventFlow -> Option LocatednessModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (LocatednessModulusUp.mk
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 0 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 1 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 2 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 3 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 4 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 5 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 6 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 7 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 8 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 9 ef))
          (locatednessModulusDecodeBHist (locatednessModulusEventAt 10 ef)))

private theorem LocatednessModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatednessModulusUp,
      locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tolerance locatedInterval rationalCells dyadic stream regSeq realSeal transport
      continuation provenance localNameCert =>
      change
        some
          (LocatednessModulusUp.mk
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist tolerance))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist locatedInterval))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist rationalCells))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist dyadic))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist stream))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist regSeq))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist realSeal))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist transport))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist continuation))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist provenance))
            (locatednessModulusDecodeBHist (locatednessModulusEncodeBHist localNameCert))) =
          some
            (LocatednessModulusUp.mk tolerance locatedInterval rationalCells dyadic stream regSeq
              realSeal transport continuation provenance localNameCert)
      rw [LocatednessModulusTasteGate_single_carrier_alignment_decode_encode tolerance,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode locatedInterval,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode rationalCells,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode dyadic,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode stream,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode regSeq,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode realSeal,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode transport,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode continuation,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatednessModulusTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem LocatednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatednessModulusUp} :
    locatednessModulusToEventFlow x = locatednessModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) =
        locatednessModulusFromEventFlow (locatednessModulusToEventFlow y) :=
    congrArg locatednessModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatednessModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatednessModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatednessModulusTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : LocatednessModulusUp, locatednessModulusFields x = locatednessModulusFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tolerance₁ locatedInterval₁ rationalCells₁ dyadic₁ stream₁ regSeq₁ realSeal₁ transport₁
      continuation₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk tolerance₂ locatedInterval₂ rationalCells₂ dyadic₂ stream₂ regSeq₂ realSeal₂ transport₂
          continuation₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance locatednessModulusBHistCarrier : BHistCarrier LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatednessModulusToEventFlow
  fromEventFlow := locatednessModulusFromEventFlow

instance locatednessModulusChapterTasteGate : ChapterTasteGate LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x
    exact LocatednessModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatednessModulusFieldFaithful : FieldFaithful LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatednessModulusFields
  field_faithful := by
    intro x y h
    change locatednessModulusFields x = locatednessModulusFields y at h
    exact LocatednessModulusTasteGate_single_carrier_alignment_field_faithful x y h

instance locatednessModulusNontrivial : Nontrivial LocatednessModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatednessModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatednessModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatednessModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatednessModulusUp) ∧
      Nonempty (FieldFaithful LocatednessModulusUp) ∧
        Nonempty (Nontrivial LocatednessModulusUp) ∧
          (∀ h : BHist, locatednessModulusDecodeBHist (locatednessModulusEncodeBHist h) = h) ∧
            (∀ x : LocatednessModulusUp,
              locatednessModulusFromEventFlow (locatednessModulusToEventFlow x) = some x) ∧
              (∀ x y : LocatednessModulusUp,
                locatednessModulusToEventFlow x = locatednessModulusToEventFlow y -> x = y) ∧
                locatednessModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨locatednessModulusChapterTasteGate⟩
  · constructor
    · exact ⟨locatednessModulusFieldFaithful⟩
    · constructor
      · exact ⟨locatednessModulusNontrivial⟩
      · constructor
        · exact LocatednessModulusTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact LocatednessModulusTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact LocatednessModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.LocatednessModulusUp.TasteGate
