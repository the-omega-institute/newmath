import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

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

inductive SeparatedMetricUp : Type where
  | mk (metric distance separation limit0 limit1 equivalence transport replay provenance
      name : BHist) : SeparatedMetricUp
  deriving DecidableEq

def separatedMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedMetricEncodeBHist h

def separatedMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedMetricDecodeBHist tail)

private theorem separatedMetric_decode_encode_bhist :
    ∀ h : BHist, separatedMetricDecodeBHist (separatedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedMetricFields : SeparatedMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedMetricUp.mk metric distance separation limit0 limit1 equivalence transport
      replay provenance name =>
      [metric, distance, separation, limit0, limit1, equivalence, transport, replay,
        provenance, name]

def separatedMetricToEventFlow : SeparatedMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separatedMetricFields x).map separatedMetricEncodeBHist

def separatedMetricFromEventFlow : EventFlow → Option SeparatedMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | metric :: distance :: separation :: limit0 :: limit1 :: equivalence :: transport ::
      replay :: provenance :: name :: [] =>
      some
        (SeparatedMetricUp.mk
          (separatedMetricDecodeBHist metric)
          (separatedMetricDecodeBHist distance)
          (separatedMetricDecodeBHist separation)
          (separatedMetricDecodeBHist limit0)
          (separatedMetricDecodeBHist limit1)
          (separatedMetricDecodeBHist equivalence)
          (separatedMetricDecodeBHist transport)
          (separatedMetricDecodeBHist replay)
          (separatedMetricDecodeBHist provenance)
          (separatedMetricDecodeBHist name))
  | _ => none

private theorem separatedMetric_round_trip :
    ∀ x : SeparatedMetricUp,
      separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric distance separation limit0 limit1 equivalence transport replay provenance name =>
      simp only [separatedMetricToEventFlow, separatedMetricFields,
        separatedMetricFromEventFlow, List.map_cons, List.map_nil,
        separatedMetric_decode_encode_bhist]

private theorem separatedMetricToEventFlow_injective {x y : SeparatedMetricUp} :
    separatedMetricToEventFlow x = separatedMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedMetricFromEventFlow (separatedMetricToEventFlow x) =
        separatedMetricFromEventFlow (separatedMetricToEventFlow y) :=
    congrArg separatedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedMetric_round_trip x).symm
      (Eq.trans hread (separatedMetric_round_trip y)))

private theorem separatedMetric_field_faithful :
    ∀ x y : SeparatedMetricUp, separatedMetricFields x = separatedMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric₁ distance₁ separation₁ limit0₁ limit1₁ equivalence₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk metric₂ distance₂ separation₂ limit0₂ limit1₂ equivalence₂ transport₂ replay₂
          provenance₂ name₂ =>
          injection hfields with hmetric tail0
          injection tail0 with hdistance tail1
          injection tail1 with hseparation tail2
          injection tail2 with hlimit0 tail3
          injection tail3 with hlimit1 tail4
          injection tail4 with hequivalence tail5
          injection tail5 with htransport tail6
          injection tail6 with hreplay tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hname _
          subst hmetric
          subst hdistance
          subst hseparation
          subst hlimit0
          subst hlimit1
          subst hequivalence
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance separatedMetricBHistCarrier : BHistCarrier SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedMetricToEventFlow
  fromEventFlow := separatedMetricFromEventFlow

instance separatedMetricChapterTasteGate : ChapterTasteGate SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x
    exact separatedMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedMetricToEventFlow_injective heq)

instance separatedMetricFieldFaithful : FieldFaithful SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedMetricFields
  field_faithful := separatedMetric_field_faithful

instance separatedMetricNontrivial : Nontrivial SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedMetricChapterTasteGate

theorem SeparatedMetricTasteGate_carrier_alignment
    (metric distance separation limit0 limit1 equivalence transport replay provenance
      name : BHist) :
    separatedMetricFields
        (SeparatedMetricUp.mk metric distance separation limit0 limit1 equivalence transport
          replay provenance name) =
      [metric, distance, separation, limit0, limit1, equivalence, transport, replay,
        provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  rfl

def SeparatedMetricPacket [AskSetup] [PackageSetup]
    (metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory metric ∧ UnaryHistory apartness ∧ UnaryHistory zeroDistance ∧
    UnaryHistory limitWitness ∧ UnaryHistory completionRoute ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ UnaryHistory endpoint ∧
        Cont apartness zeroDistance limitWitness ∧
          Cont limitWitness completionRoute transport ∧
            Cont transport provenance endpoint ∧ PkgSig bundle nameCert pkg

theorem SeparatedMetricPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute
            transport provenance nameCert endpoint bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute
            transport provenance nameCert endpoint bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute
            transport provenance nameCert endpoint bundle pkg ∧ hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert ⟨packet, hsame_refl nameCert⟩
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
        intro row other sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.SeparatedMetricUp
