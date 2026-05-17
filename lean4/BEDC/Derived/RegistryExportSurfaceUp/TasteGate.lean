import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryExportSurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryExportSurfaceUp : Type where
  | mk :
      (carrier exportLayer registryLayer claimLayer verifierLayer publicSurface nonescape
        tasteGate : BHist) →
      RegistryExportSurfaceUp
  deriving DecidableEq

def registryExportSurfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: registryExportSurfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: registryExportSurfaceEncodeBHist h

def registryExportSurfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (registryExportSurfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (registryExportSurfaceDecodeBHist tail)

private def registryExportSurfaceNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => registryExportSurfaceNthRawEvent tail n

private theorem registryExportSurface_decode_encode_bhist :
    ∀ h : BHist, registryExportSurfaceDecodeBHist
      (registryExportSurfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem registryExportSurface_mk_congr
    {carrier carrier' exportLayer exportLayer' registryLayer registryLayer' claimLayer
      claimLayer' verifierLayer verifierLayer' publicSurface publicSurface' nonescape
      nonescape' tasteGate tasteGate' : BHist}
    (hCarrier : carrier' = carrier)
    (hExportLayer : exportLayer' = exportLayer)
    (hRegistryLayer : registryLayer' = registryLayer)
    (hClaimLayer : claimLayer' = claimLayer)
    (hVerifierLayer : verifierLayer' = verifierLayer)
    (hPublicSurface : publicSurface' = publicSurface)
    (hNonescape : nonescape' = nonescape)
    (hTasteGate : tasteGate' = tasteGate) :
    RegistryExportSurfaceUp.mk carrier' exportLayer' registryLayer' claimLayer'
        verifierLayer' publicSurface' nonescape' tasteGate' =
      RegistryExportSurfaceUp.mk carrier exportLayer registryLayer claimLayer
        verifierLayer publicSurface nonescape tasteGate := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCarrier
  cases hExportLayer
  cases hRegistryLayer
  cases hClaimLayer
  cases hVerifierLayer
  cases hPublicSurface
  cases hNonescape
  cases hTasteGate
  rfl

def registryExportSurfaceFields : RegistryExportSurfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryExportSurfaceUp.mk carrier exportLayer registryLayer claimLayer verifierLayer
      publicSurface nonescape tasteGate =>
      [carrier, exportLayer, registryLayer, claimLayer, verifierLayer, publicSurface,
        nonescape, tasteGate]

def registryExportSurfaceToEventFlow : RegistryExportSurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryExportSurfaceUp.mk carrier exportLayer registryLayer claimLayer verifierLayer
      publicSurface nonescape tasteGate =>
      [registryExportSurfaceEncodeBHist carrier,
        registryExportSurfaceEncodeBHist exportLayer,
        registryExportSurfaceEncodeBHist registryLayer,
        registryExportSurfaceEncodeBHist claimLayer,
        registryExportSurfaceEncodeBHist verifierLayer,
        registryExportSurfaceEncodeBHist publicSurface,
        registryExportSurfaceEncodeBHist nonescape,
        registryExportSurfaceEncodeBHist tasteGate]

def registryExportSurfaceFromEventFlow (ef : EventFlow) : Option RegistryExportSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegistryExportSurfaceUp.mk
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 0))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 1))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 2))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 3))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 4))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 5))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 6))
      (registryExportSurfaceDecodeBHist (registryExportSurfaceNthRawEvent ef 7)))

private theorem registryExportSurface_round_trip :
    ∀ x : RegistryExportSurfaceUp,
      registryExportSurfaceFromEventFlow (registryExportSurfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier exportLayer registryLayer claimLayer verifierLayer publicSurface nonescape
      tasteGate =>
      exact
        congrArg some
          (registryExportSurface_mk_congr
            (registryExportSurface_decode_encode_bhist carrier)
            (registryExportSurface_decode_encode_bhist exportLayer)
            (registryExportSurface_decode_encode_bhist registryLayer)
            (registryExportSurface_decode_encode_bhist claimLayer)
            (registryExportSurface_decode_encode_bhist verifierLayer)
            (registryExportSurface_decode_encode_bhist publicSurface)
            (registryExportSurface_decode_encode_bhist nonescape)
            (registryExportSurface_decode_encode_bhist tasteGate))

private theorem registryExportSurfaceToEventFlow_injective {x y : RegistryExportSurfaceUp} :
    registryExportSurfaceToEventFlow x = registryExportSurfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      registryExportSurfaceFromEventFlow (registryExportSurfaceToEventFlow x) =
        registryExportSurfaceFromEventFlow (registryExportSurfaceToEventFlow y) :=
    congrArg registryExportSurfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (registryExportSurface_round_trip x).symm
      (Eq.trans hread (registryExportSurface_round_trip y)))

private theorem registryExportSurface_field_faithful :
    ∀ x y : RegistryExportSurfaceUp, registryExportSurfaceFields x =
      registryExportSurfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk carrier exportLayer registryLayer claimLayer verifierLayer publicSurface nonescape
      tasteGate =>
      cases y with
      | mk carrier' exportLayer' registryLayer' claimLayer' verifierLayer' publicSurface'
          nonescape' tasteGate' =>
          cases hfields
          rfl

instance registryExportSurfaceBHistCarrier : BHistCarrier RegistryExportSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := registryExportSurfaceToEventFlow
  fromEventFlow := registryExportSurfaceFromEventFlow

instance registryExportSurfaceChapterTasteGate :
    ChapterTasteGate RegistryExportSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change registryExportSurfaceFromEventFlow
      (registryExportSurfaceToEventFlow x) = some x
    exact registryExportSurface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (registryExportSurfaceToEventFlow_injective heq)

instance registryExportSurfaceFieldFaithful : FieldFaithful RegistryExportSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := registryExportSurfaceFields
  field_faithful := registryExportSurface_field_faithful

instance registryExportSurfaceNontrivial : Nontrivial RegistryExportSurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryExportSurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegistryExportSurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegistryExportSurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  registryExportSurfaceChapterTasteGate

end BEDC.Derived.RegistryExportSurfaceUp
