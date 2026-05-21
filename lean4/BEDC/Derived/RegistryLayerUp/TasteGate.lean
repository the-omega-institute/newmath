import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryLayerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryLayerUp : Type where
  | mk :
      (concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade formalTarget
        exportControl transport packageProvenance name : BHist) →
      RegistryLayerUp
  deriving DecidableEq

def registryLayerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: registryLayerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: registryLayerEncodeBHist h

def registryLayerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (registryLayerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (registryLayerDecodeBHist tail)

private def registryLayerNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => registryLayerNthRawEvent tail n

private theorem registryLayer_decode_encode_bhist :
    ∀ h : BHist, registryLayerDecodeBHist (registryLayerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem registryLayer_mk_congr
    {concept concept' theoremRow theoremRow' gapRow gapRow' traditionRow traditionRow'
      scienceRow scienceRow' cannotClaim cannotClaim' upgrade upgrade'
      formalTarget formalTarget' exportControl exportControl' transport transport'
      packageProvenance packageProvenance' name name' : BHist}
    (hConcept : concept' = concept)
    (hTheoremRow : theoremRow' = theoremRow)
    (hGapRow : gapRow' = gapRow)
    (hTraditionRow : traditionRow' = traditionRow)
    (hScienceRow : scienceRow' = scienceRow)
    (hCannotClaim : cannotClaim' = cannotClaim)
    (hUpgrade : upgrade' = upgrade)
    (hFormalTarget : formalTarget' = formalTarget)
    (hExportControl : exportControl' = exportControl)
    (hTransport : transport' = transport)
    (hPackageProvenance : packageProvenance' = packageProvenance)
    (hName : name' = name) :
    RegistryLayerUp.mk concept' theoremRow' gapRow' traditionRow' scienceRow' cannotClaim'
        upgrade' formalTarget' exportControl' transport' packageProvenance' name' =
      RegistryLayerUp.mk concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade
        formalTarget exportControl transport packageProvenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hConcept
  cases hTheoremRow
  cases hGapRow
  cases hTraditionRow
  cases hScienceRow
  cases hCannotClaim
  cases hUpgrade
  cases hFormalTarget
  cases hExportControl
  cases hTransport
  cases hPackageProvenance
  cases hName
  rfl

def registryLayerFields : RegistryLayerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryLayerUp.mk concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade
      formalTarget exportControl transport packageProvenance name =>
      [concept, theoremRow, gapRow, traditionRow, scienceRow, cannotClaim, upgrade,
        formalTarget, exportControl, transport, packageProvenance, name]

def registryLayerToEventFlow : RegistryLayerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryLayerUp.mk concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade
      formalTarget exportControl transport packageProvenance name =>
      [registryLayerEncodeBHist concept,
        registryLayerEncodeBHist theoremRow,
        registryLayerEncodeBHist gapRow,
        registryLayerEncodeBHist traditionRow,
        registryLayerEncodeBHist scienceRow,
        registryLayerEncodeBHist cannotClaim,
        registryLayerEncodeBHist upgrade,
        registryLayerEncodeBHist formalTarget,
        registryLayerEncodeBHist exportControl,
        registryLayerEncodeBHist transport,
        registryLayerEncodeBHist packageProvenance,
        registryLayerEncodeBHist name]

def registryLayerFromEventFlow (ef : EventFlow) : Option RegistryLayerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegistryLayerUp.mk
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 0))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 1))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 2))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 3))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 4))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 5))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 6))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 7))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 8))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 9))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 10))
      (registryLayerDecodeBHist (registryLayerNthRawEvent ef 11)))

private theorem registryLayer_round_trip :
    ∀ x : RegistryLayerUp,
      registryLayerFromEventFlow (registryLayerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade formalTarget
      exportControl transport packageProvenance name =>
      exact
        congrArg some
          (registryLayer_mk_congr
            (registryLayer_decode_encode_bhist concept)
            (registryLayer_decode_encode_bhist theoremRow)
            (registryLayer_decode_encode_bhist gapRow)
            (registryLayer_decode_encode_bhist traditionRow)
            (registryLayer_decode_encode_bhist scienceRow)
            (registryLayer_decode_encode_bhist cannotClaim)
            (registryLayer_decode_encode_bhist upgrade)
            (registryLayer_decode_encode_bhist formalTarget)
            (registryLayer_decode_encode_bhist exportControl)
            (registryLayer_decode_encode_bhist transport)
            (registryLayer_decode_encode_bhist packageProvenance)
            (registryLayer_decode_encode_bhist name))

private theorem registryLayerToEventFlow_injective {x y : RegistryLayerUp} :
    registryLayerToEventFlow x = registryLayerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      registryLayerFromEventFlow (registryLayerToEventFlow x) =
        registryLayerFromEventFlow (registryLayerToEventFlow y) :=
    congrArg registryLayerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (registryLayer_round_trip x).symm
      (Eq.trans hread (registryLayer_round_trip y)))

private theorem registryLayer_field_faithful :
    ∀ x y : RegistryLayerUp, registryLayerFields x = registryLayerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk concept theoremRow gapRow traditionRow scienceRow cannotClaim upgrade formalTarget
      exportControl transport packageProvenance name =>
      cases y with
      | mk concept' theoremRow' gapRow' traditionRow' scienceRow' cannotClaim' upgrade'
          formalTarget' exportControl' transport' packageProvenance' name' =>
          cases hfields
          rfl

instance registryLayerBHistCarrier : BHistCarrier RegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := registryLayerToEventFlow
  fromEventFlow := registryLayerFromEventFlow

instance registryLayerChapterTasteGate : ChapterTasteGate RegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change registryLayerFromEventFlow (registryLayerToEventFlow x) = some x
    exact registryLayer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (registryLayerToEventFlow_injective heq)

instance registryLayerFieldFaithful : FieldFaithful RegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := registryLayerFields
  field_faithful := registryLayer_field_faithful

instance registryLayerNontrivial : Nontrivial RegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryLayerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegistryLayerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegistryLayerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  registryLayerChapterTasteGate

theorem RegistryLayerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegistryLayerUp) ∧
      Nonempty (FieldFaithful RegistryLayerUp) ∧
        Nonempty (Nontrivial RegistryLayerUp) ∧
          (∀ x : RegistryLayerUp, ∃ rows : List BHist, rows = FieldFaithful.fields x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨registryLayerChapterTasteGate⟩
  · constructor
    · exact ⟨registryLayerFieldFaithful⟩
    · constructor
      · exact ⟨registryLayerNontrivial⟩
      · intro x
        exact ⟨FieldFaithful.fields x, rfl⟩

theorem RegistryLayer_export_control_exactness :
    (∀ C T G D S K U A F H P N : BHist,
      registryLayerFields (RegistryLayerUp.mk C T G D S K U A F H P N) =
        [C, T, G, D, S, K, U, A, F, H, P, N]) ∧
      (∀ x y : RegistryLayerUp, registryLayerFields x = registryLayerFields y → x = y) ∧
        RegistryLayerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty ≠
          RegistryLayerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro C T G D S K U A F H P N
    rfl
  · constructor
    · exact registryLayer_field_faithful
    · intro h
      cases h

end BEDC.Derived.RegistryLayerUp
