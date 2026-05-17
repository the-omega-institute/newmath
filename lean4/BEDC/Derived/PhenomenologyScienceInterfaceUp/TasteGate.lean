import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhenomenologyScienceInterfaceUp : Type where
  | mk
      (records universeSlice observerIdentity locality scientificObject scienceBridge
        standardBridge gapLedger transport replay provenance localName : BHist) :
      PhenomenologyScienceInterfaceUp
  deriving DecidableEq

def phenomenologyScienceInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phenomenologyScienceInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phenomenologyScienceInterfaceEncodeBHist h

def phenomenologyScienceInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phenomenologyScienceInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phenomenologyScienceInterfaceDecodeBHist tail)

private theorem phenomenologyScienceInterfaceDecode_encode_bhist :
    ∀ h : BHist,
      phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def phenomenologyScienceInterfaceToEventFlow :
    PhenomenologyScienceInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhenomenologyScienceInterfaceUp.mk records universeSlice observerIdentity locality
      scientificObject scienceBridge standardBridge gapLedger transport replay provenance
      localName =>
      [[BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist records,
        [BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist universeSlice,
        [BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist observerIdentity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist scientificObject,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist scienceBridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist standardBridge,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist gapLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist localName]

def phenomenologyScienceInterfaceFromEventFlow :
    EventFlow → Option PhenomenologyScienceInterfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: records :: _tag1 :: universeSlice :: _tag2 :: observerIdentity :: _tag3 ::
      locality :: _tag4 :: scientificObject :: _tag5 :: scienceBridge :: _tag6 ::
        standardBridge :: _tag7 :: gapLedger :: _tag8 :: transport :: _tag9 ::
          replay :: _tag10 :: provenance :: _tag11 :: localName :: [] =>
      some
        (PhenomenologyScienceInterfaceUp.mk
          (phenomenologyScienceInterfaceDecodeBHist records)
          (phenomenologyScienceInterfaceDecodeBHist universeSlice)
          (phenomenologyScienceInterfaceDecodeBHist observerIdentity)
          (phenomenologyScienceInterfaceDecodeBHist locality)
          (phenomenologyScienceInterfaceDecodeBHist scientificObject)
          (phenomenologyScienceInterfaceDecodeBHist scienceBridge)
          (phenomenologyScienceInterfaceDecodeBHist standardBridge)
          (phenomenologyScienceInterfaceDecodeBHist gapLedger)
          (phenomenologyScienceInterfaceDecodeBHist transport)
          (phenomenologyScienceInterfaceDecodeBHist replay)
          (phenomenologyScienceInterfaceDecodeBHist provenance)
          (phenomenologyScienceInterfaceDecodeBHist localName))
  | _ => none

private theorem phenomenologyScienceInterface_round_trip :
    ∀ x : PhenomenologyScienceInterfaceUp,
      phenomenologyScienceInterfaceFromEventFlow
        (phenomenologyScienceInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk records universeSlice observerIdentity locality scientificObject scienceBridge
      standardBridge gapLedger transport replay provenance localName =>
      change
        some
          (PhenomenologyScienceInterfaceUp.mk
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist records))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist universeSlice))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist observerIdentity))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist locality))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist scientificObject))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist scienceBridge))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist standardBridge))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist gapLedger))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist transport))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist replay))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist provenance))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist localName))) =
          some
            (PhenomenologyScienceInterfaceUp.mk records universeSlice observerIdentity
              locality scientificObject scienceBridge standardBridge gapLedger transport
              replay provenance localName)
      rw [phenomenologyScienceInterfaceDecode_encode_bhist records,
        phenomenologyScienceInterfaceDecode_encode_bhist universeSlice,
        phenomenologyScienceInterfaceDecode_encode_bhist observerIdentity,
        phenomenologyScienceInterfaceDecode_encode_bhist locality,
        phenomenologyScienceInterfaceDecode_encode_bhist scientificObject,
        phenomenologyScienceInterfaceDecode_encode_bhist scienceBridge,
        phenomenologyScienceInterfaceDecode_encode_bhist standardBridge,
        phenomenologyScienceInterfaceDecode_encode_bhist gapLedger,
        phenomenologyScienceInterfaceDecode_encode_bhist transport,
        phenomenologyScienceInterfaceDecode_encode_bhist replay,
        phenomenologyScienceInterfaceDecode_encode_bhist provenance,
        phenomenologyScienceInterfaceDecode_encode_bhist localName]

private theorem phenomenologyScienceInterfaceToEventFlow_injective
    {x y : PhenomenologyScienceInterfaceUp} :
    phenomenologyScienceInterfaceToEventFlow x =
        phenomenologyScienceInterfaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phenomenologyScienceInterfaceFromEventFlow
          (phenomenologyScienceInterfaceToEventFlow x) =
        phenomenologyScienceInterfaceFromEventFlow
          (phenomenologyScienceInterfaceToEventFlow y) :=
    congrArg phenomenologyScienceInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (phenomenologyScienceInterface_round_trip x).symm
      (Eq.trans hread (phenomenologyScienceInterface_round_trip y)))

instance phenomenologyScienceInterfaceBHistCarrier :
    BHistCarrier PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phenomenologyScienceInterfaceToEventFlow
  fromEventFlow := phenomenologyScienceInterfaceFromEventFlow

instance phenomenologyScienceInterfaceChapterTasteGate :
    ChapterTasteGate PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      phenomenologyScienceInterfaceFromEventFlow
        (phenomenologyScienceInterfaceToEventFlow x) = some x
    exact phenomenologyScienceInterface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (phenomenologyScienceInterfaceToEventFlow_injective heq)

instance phenomenologyScienceInterfaceFieldFaithful :
    FieldFaithful PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PhenomenologyScienceInterfaceUp.mk records universeSlice observerIdentity locality
        scientificObject scienceBridge standardBridge gapLedger transport replay provenance
        localName =>
        [records, universeSlice, observerIdentity, locality, scientificObject, scienceBridge,
          standardBridge, gapLedger, transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk records₁ universeSlice₁ observerIdentity₁ locality₁ scientificObject₁ scienceBridge₁
        standardBridge₁ gapLedger₁ transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | mk records₂ universeSlice₂ observerIdentity₂ locality₂ scientificObject₂ scienceBridge₂
            standardBridge₂ gapLedger₂ transport₂ replay₂ provenance₂ localName₂ =>
            simp only [] at h
            cases h
            rfl

instance phenomenologyScienceInterfaceNontrivial :
    Nontrivial PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhenomenologyScienceInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhenomenologyScienceInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhenomenologyScienceInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  phenomenologyScienceInterfaceChapterTasteGate

end BEDC.Derived.PhenomenologyScienceInterfaceUp
