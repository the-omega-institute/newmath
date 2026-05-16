import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TowerEndpointReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TowerEndpointReflectionUp : Type where
  | mk :
      (endpoint source towerCompression endpointEquivalence ledgerFunctor descentAudit
        obstruction transport replay provenance localName : BHist) →
      TowerEndpointReflectionUp
  deriving DecidableEq

def towerEndpointReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: towerEndpointReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: towerEndpointReflectionEncodeBHist h

def towerEndpointReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (towerEndpointReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (towerEndpointReflectionDecodeBHist tail)

private theorem towerEndpointReflectionDecodeEncodeBHist :
    ∀ h : BHist,
      towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def towerEndpointReflectionFields : TowerEndpointReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TowerEndpointReflectionUp.mk endpoint source towerCompression endpointEquivalence
      ledgerFunctor descentAudit obstruction transport replay provenance localName =>
      [endpoint, source, towerCompression, endpointEquivalence, ledgerFunctor, descentAudit,
        obstruction, transport, replay, provenance, localName]

def towerEndpointReflectionToEventFlow : TowerEndpointReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (towerEndpointReflectionFields x).map towerEndpointReflectionEncodeBHist

def towerEndpointReflectionFromEventFlow : EventFlow → Option TowerEndpointReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | endpoint :: source :: towerCompression :: endpointEquivalence :: ledgerFunctor ::
      descentAudit :: obstruction :: transport :: replay :: provenance :: localName :: [] =>
      some
        (TowerEndpointReflectionUp.mk
          (towerEndpointReflectionDecodeBHist endpoint)
          (towerEndpointReflectionDecodeBHist source)
          (towerEndpointReflectionDecodeBHist towerCompression)
          (towerEndpointReflectionDecodeBHist endpointEquivalence)
          (towerEndpointReflectionDecodeBHist ledgerFunctor)
          (towerEndpointReflectionDecodeBHist descentAudit)
          (towerEndpointReflectionDecodeBHist obstruction)
          (towerEndpointReflectionDecodeBHist transport)
          (towerEndpointReflectionDecodeBHist replay)
          (towerEndpointReflectionDecodeBHist provenance)
          (towerEndpointReflectionDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem towerEndpointReflection_round_trip :
    ∀ x : TowerEndpointReflectionUp,
      towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk endpoint source towerCompression endpointEquivalence ledgerFunctor descentAudit
      obstruction transport replay provenance localName =>
      change
        some
          (TowerEndpointReflectionUp.mk
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist endpoint))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist source))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist towerCompression))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist endpointEquivalence))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist ledgerFunctor))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist descentAudit))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist obstruction))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist transport))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist replay))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist provenance))
            (towerEndpointReflectionDecodeBHist
              (towerEndpointReflectionEncodeBHist localName))) =
          some
            (TowerEndpointReflectionUp.mk endpoint source towerCompression endpointEquivalence
              ledgerFunctor descentAudit obstruction transport replay provenance localName)
      rw [towerEndpointReflectionDecodeEncodeBHist endpoint,
        towerEndpointReflectionDecodeEncodeBHist source,
        towerEndpointReflectionDecodeEncodeBHist towerCompression,
        towerEndpointReflectionDecodeEncodeBHist endpointEquivalence,
        towerEndpointReflectionDecodeEncodeBHist ledgerFunctor,
        towerEndpointReflectionDecodeEncodeBHist descentAudit,
        towerEndpointReflectionDecodeEncodeBHist obstruction,
        towerEndpointReflectionDecodeEncodeBHist transport,
        towerEndpointReflectionDecodeEncodeBHist replay,
        towerEndpointReflectionDecodeEncodeBHist provenance,
        towerEndpointReflectionDecodeEncodeBHist localName]

private theorem towerEndpointReflectionToEventFlow_injective
    {x y : TowerEndpointReflectionUp} :
    towerEndpointReflectionToEventFlow x = towerEndpointReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) =
        towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow y) :=
    congrArg towerEndpointReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (towerEndpointReflection_round_trip x).symm
      (Eq.trans hread (towerEndpointReflection_round_trip y)))

private theorem towerEndpointReflection_fields_faithful :
    ∀ x y : TowerEndpointReflectionUp,
      towerEndpointReflectionFields x = towerEndpointReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk endpoint₁ source₁ towerCompression₁ endpointEquivalence₁ ledgerFunctor₁
      descentAudit₁ obstruction₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk endpoint₂ source₂ towerCompression₂ endpointEquivalence₂ ledgerFunctor₂
          descentAudit₂ obstruction₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance towerEndpointReflectionBHistCarrier : BHistCarrier TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := towerEndpointReflectionToEventFlow
  fromEventFlow := towerEndpointReflectionFromEventFlow

instance towerEndpointReflectionChapterTasteGate :
    ChapterTasteGate TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) = some x
    exact towerEndpointReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (towerEndpointReflectionToEventFlow_injective heq)

instance towerEndpointReflectionFieldFaithful :
    FieldFaithful TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := towerEndpointReflectionFields
  field_faithful := towerEndpointReflection_fields_faithful

instance towerEndpointReflectionNontrivial : Nontrivial TowerEndpointReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TowerEndpointReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TowerEndpointReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TowerEndpointReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  towerEndpointReflectionChapterTasteGate

theorem TowerEndpointReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, towerEndpointReflectionDecodeBHist (towerEndpointReflectionEncodeBHist h) = h) ∧
      (∀ x : TowerEndpointReflectionUp,
        towerEndpointReflectionFromEventFlow (towerEndpointReflectionToEventFlow x) = some x) ∧
        (∀ x y : TowerEndpointReflectionUp,
          towerEndpointReflectionToEventFlow x = towerEndpointReflectionToEventFlow y → x = y) ∧
          towerEndpointReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact towerEndpointReflectionDecodeEncodeBHist
  · constructor
    · exact towerEndpointReflection_round_trip
    · constructor
      · intro x y heq
        exact towerEndpointReflectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.TowerEndpointReflectionUp
