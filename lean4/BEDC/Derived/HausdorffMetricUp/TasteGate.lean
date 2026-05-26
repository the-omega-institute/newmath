import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def HausdorffMetricCarrier [AskSetup] [PackageSetup]
    (subsetA subsetB metric compactRows finiteNets distanceRows symmetricBounds transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory subsetA ∧ UnaryHistory subsetB ∧ UnaryHistory metric ∧
    UnaryHistory compactRows ∧ UnaryHistory finiteNets ∧ UnaryHistory distanceRows ∧
      UnaryHistory symmetricBounds ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont subsetA subsetB metric ∧ Cont compactRows finiteNets distanceRows ∧
            Cont distanceRows symmetricBounds replay ∧ PkgSig bundle provenance pkg

theorem HausdorffMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {subsetA subsetB metric compactRows finiteNets distanceRows symmetricBounds transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffMetricCarrier subsetA subsetB metric compactRows finiteNets distanceRows
        symmetricBounds transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HausdorffMetricCarrier subsetA subsetB metric compactRows finiteNets distanceRows
            symmetricBounds transport replay provenance localName bundle pkg ∧
              hsame row localName)
        (fun row : BHist =>
          hsame row localName ∧ Cont subsetA subsetB metric ∧
            Cont compactRows finiteNets distanceRows ∧
              Cont distanceRows symmetricBounds replay)
        (fun row : BHist =>
          hsame row localName ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert Cont UnaryHistory
  intro carrier
  let carrierSource := carrier
  obtain ⟨_subsetAUnary, _subsetBUnary, _metricUnary, _compactRowsUnary,
    _finiteNetsUnary, _distanceRowsUnary, _symmetricBoundsUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, subsetMetricRoute,
    netDistanceRoute, distanceReplayRoute, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, subsetMetricRoute, netDistanceRoute, distanceReplayRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

inductive HausdorffMetricUp : Type where
  | packet
      (subsetA subsetB metric compactRows netRows distanceRows boundRows transport replay
        provenance localName : BHist) :
      HausdorffMetricUp
  deriving DecidableEq

def HausdorffMetricUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: HausdorffMetricUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: HausdorffMetricUp_encodeBHist h

def HausdorffMetricUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (HausdorffMetricUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (HausdorffMetricUp_decodeBHist tail)

private theorem HausdorffMetricUp_decode_encode :
    ∀ h : BHist, HausdorffMetricUp_decodeBHist (HausdorffMetricUp_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def HausdorffMetricUp_fields : HausdorffMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffMetricUp.packet subsetA subsetB metric compactRows netRows distanceRows
      boundRows transport replay provenance localName =>
      [subsetA, subsetB, metric, compactRows, netRows, distanceRows, boundRows, transport,
        replay, provenance, localName]

def HausdorffMetricUp_toEventFlow : HausdorffMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (HausdorffMetricUp_fields x).map HausdorffMetricUp_encodeBHist

def HausdorffMetricUp_fromEventFlow : EventFlow → Option HausdorffMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | subsetA :: subsetB :: metric :: compactRows :: netRows :: distanceRows :: boundRows ::
      transport :: replay :: provenance :: localName :: [] =>
      some
        (HausdorffMetricUp.packet
          (HausdorffMetricUp_decodeBHist subsetA)
          (HausdorffMetricUp_decodeBHist subsetB)
          (HausdorffMetricUp_decodeBHist metric)
          (HausdorffMetricUp_decodeBHist compactRows)
          (HausdorffMetricUp_decodeBHist netRows)
          (HausdorffMetricUp_decodeBHist distanceRows)
          (HausdorffMetricUp_decodeBHist boundRows)
          (HausdorffMetricUp_decodeBHist transport)
          (HausdorffMetricUp_decodeBHist replay)
          (HausdorffMetricUp_decodeBHist provenance)
          (HausdorffMetricUp_decodeBHist localName))
  | _ => none

private theorem HausdorffMetricUp_round_trip :
    ∀ x : HausdorffMetricUp,
      HausdorffMetricUp_fromEventFlow (HausdorffMetricUp_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | packet subsetA subsetB metric compactRows netRows distanceRows boundRows transport replay
      provenance localName =>
      simp only [HausdorffMetricUp_toEventFlow, HausdorffMetricUp_fields,
        HausdorffMetricUp_fromEventFlow, List.map_cons, List.map_nil,
        HausdorffMetricUp_decode_encode]

private theorem HausdorffMetricUp_toEventFlow_injective {x y : HausdorffMetricUp} :
    HausdorffMetricUp_toEventFlow x = HausdorffMetricUp_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = HausdorffMetricUp_fromEventFlow (HausdorffMetricUp_toEventFlow x) :=
        (HausdorffMetricUp_round_trip x).symm
      _ = HausdorffMetricUp_fromEventFlow (HausdorffMetricUp_toEventFlow y) :=
        congrArg HausdorffMetricUp_fromEventFlow hxy
      _ = some y := HausdorffMetricUp_round_trip y
  exact Option.some.inj optionEq

instance HausdorffMetricUp_BHistCarrier : BHistCarrier HausdorffMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := HausdorffMetricUp_toEventFlow
  fromEventFlow := HausdorffMetricUp_fromEventFlow

instance HausdorffMetricUp_ChapterTasteGate : ChapterTasteGate HausdorffMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change HausdorffMetricUp_fromEventFlow (HausdorffMetricUp_toEventFlow x) = some x
    exact HausdorffMetricUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffMetricUp_toEventFlow_injective heq)

instance HausdorffMetricUp_Nontrivial : Nontrivial HausdorffMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffMetricUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffMetricUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HausdorffMetricUp_taste_gate : ChapterTasteGate HausdorffMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HausdorffMetricUp_ChapterTasteGate

theorem HausdorffMetricUp_single_carrier_alignment :
    (∀ h : BHist, HausdorffMetricUp_decodeBHist (HausdorffMetricUp_encodeBHist h) = h) ∧
      HausdorffMetricUp_fields
          (HausdorffMetricUp.packet BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨HausdorffMetricUp_decode_encode, rfl⟩

end BEDC.Derived.HausdorffMetricUp
