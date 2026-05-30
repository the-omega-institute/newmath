import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalTailMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalTailMapUp : Type where
  | mk (source target sourceService targetService monotone transport route provenance cert :
      BHist) : CofinalTailMapUp
  deriving DecidableEq

def cofinalTailMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalTailMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalTailMapEncodeBHist h

def cofinalTailMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalTailMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalTailMapDecodeBHist tail)

private theorem CofinalTailMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalTailMapFields : CofinalTailMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalTailMapUp.mk source target sourceService targetService monotone transport route
      provenance cert =>
      [source, target, sourceService, targetService, monotone, transport, route, provenance, cert]

def cofinalTailMapToEventFlow : CofinalTailMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cofinalTailMapFields x).map cofinalTailMapEncodeBHist

private def cofinalTailMapEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cofinalTailMapEventAt index rest

def cofinalTailMapFromEventFlow (ef : EventFlow) : Option CofinalTailMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalTailMapUp.mk
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 0 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 1 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 2 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 3 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 4 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 5 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 6 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 7 ef))
      (cofinalTailMapDecodeBHist (cofinalTailMapEventAt 8 ef)))

private theorem CofinalTailMapTasteGate_single_carrier_alignment_round_trip
    (x : CofinalTailMapUp) :
    cofinalTailMapFromEventFlow (cofinalTailMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source target sourceService targetService monotone transport route provenance cert =>
      change
        some
          (CofinalTailMapUp.mk
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist source))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist target))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist sourceService))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist targetService))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist monotone))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist transport))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist route))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist provenance))
            (cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist cert))) =
          some
            (CofinalTailMapUp.mk source target sourceService targetService monotone transport
              route provenance cert)
      rw [CofinalTailMapTasteGate_single_carrier_alignment_decode_encode source,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode target,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode sourceService,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode targetService,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode monotone,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode transport,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode route,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode provenance,
        CofinalTailMapTasteGate_single_carrier_alignment_decode_encode cert]

private theorem CofinalTailMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CofinalTailMapUp} :
    cofinalTailMapToEventFlow x = cofinalTailMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalTailMapFromEventFlow (cofinalTailMapToEventFlow x) =
        cofinalTailMapFromEventFlow (cofinalTailMapToEventFlow y) :=
    congrArg cofinalTailMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CofinalTailMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CofinalTailMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem CofinalTailMapTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CofinalTailMapUp, cofinalTailMapFields x = cofinalTailMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ target₁ sourceService₁ targetService₁ monotone₁ transport₁ route₁ provenance₁
      cert₁ =>
      cases y with
      | mk source₂ target₂ sourceService₂ targetService₂ monotone₂ transport₂ route₂
          provenance₂ cert₂ =>
          cases hfields
          rfl

instance cofinalTailMapBHistCarrier : BHistCarrier CofinalTailMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalTailMapToEventFlow
  fromEventFlow := cofinalTailMapFromEventFlow

instance cofinalTailMapChapterTasteGate : ChapterTasteGate CofinalTailMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalTailMapFromEventFlow (cofinalTailMapToEventFlow x) = some x
    exact CofinalTailMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalTailMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cofinalTailMapFieldFaithful : FieldFaithful CofinalTailMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalTailMapFields
  field_faithful := CofinalTailMapTasteGate_single_carrier_alignment_fields_faithful

instance cofinalTailMapNontrivial : Nontrivial CofinalTailMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalTailMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalTailMapUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CofinalTailMapTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CofinalTailMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalTailMapChapterTasteGate

theorem CofinalTailMapTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalTailMapDecodeBHist (cofinalTailMapEncodeBHist h) = h) ∧
      cofinalTailMapFields
          (CofinalTailMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨CofinalTailMapTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CofinalTailMapUp
