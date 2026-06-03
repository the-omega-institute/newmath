import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionRouteTriangleUp

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

def SubjectReductionRouteTriangleCarrier [AskSetup] [PackageSetup]
    (B S F E O L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory E ∧
    UnaryHistory O ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont B C E ∧ Cont O C L ∧
        hsame E H ∧ PkgSig bundle P pkg

theorem SubjectReductionRouteTriangle_bundle_projection [AskSetup] [PackageSetup]
    {B S F E O L H C P N bundleEndpoint : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    SubjectReductionRouteTriangleCarrier B S F E O L H C P N bundle pkg →
      Cont B C bundleEndpoint →
        PkgSig bundle bundleEndpoint pkg →
          UnaryHistory B ∧ UnaryHistory bundleEndpoint ∧ Cont B C bundleEndpoint ∧
            PkgSig bundle bundleEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier bundleRoute bundlePkg
  obtain ⟨bundleUnary, _setupUnary, _conversionUnary, _endpointUnary, _obstructionUnary,
    _ledgerUnary, _transportUnary, componentUnary, _provenanceUnary, _nameUnary,
    _bundleEndpointRoute, _obstructionLedgerRoute, _endpointTransport, _carrierPkg⟩ :=
    carrier
  have bundleEndpointUnary : UnaryHistory bundleEndpoint :=
    unary_cont_closed bundleUnary componentUnary bundleRoute
  exact ⟨bundleUnary, bundleEndpointUnary, bundleRoute, bundlePkg⟩

theorem SubjectReductionRouteTriangle_obstruction_boundary [AskSetup] [PackageSetup]
    {B S F E O L H C P N endpointRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteTriangleCarrier B S F E O L H C P N bundle pkg →
      Cont B C endpointRead →
        Cont O C obstructionRead →
          PkgSig bundle endpointRead pkg →
            PkgSig bundle obstructionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row O ∨ hsame row L ∨ hsame row obstructionRead ∨
                      hsame row endpointRead)
                  (fun row : BHist =>
                    hsame row obstructionRead ∧ Cont O C obstructionRead ∧
                      PkgSig bundle obstructionRead pkg)
                  hsame ∧
                UnaryHistory endpointRead ∧ UnaryHistory obstructionRead ∧ hsame E H := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier endpointRoute obstructionRoute _endpointPkg obstructionPkg
  obtain ⟨bundleUnary, _setupUnary, _conversionUnary, _endpointUnary, obstructionUnary,
    _ledgerUnary, _transportUnary, componentUnary, _provenanceUnary, _nameUnary,
    _bundleEndpointRoute, _obstructionLedgerRoute, endpointTransport, _carrierPkg⟩ :=
    carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed bundleUnary componentUnary endpointRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary componentUnary obstructionRoute
  have sourceObstruction :
      (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row) obstructionRead := by
    exact ⟨hsame_refl obstructionRead, obstructionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row L ∨ hsame row obstructionRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            hsame row obstructionRead ∧ Cont O C obstructionRead ∧
              PkgSig bundle obstructionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obstructionRead sourceObstruction
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, obstructionRoute, obstructionPkg⟩
  }
  exact ⟨cert, endpointUnary, obstructionReadUnary, endpointTransport⟩

inductive SubjectReductionRouteTriangleUp : Type where
  | mk (B E O L H C P N : BHist) : SubjectReductionRouteTriangleUp
  deriving DecidableEq

def subjectReductionRouteTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionRouteTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionRouteTriangleEncodeBHist h

def subjectReductionRouteTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionRouteTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionRouteTriangleDecodeBHist tail)

private theorem subjectReductionRouteTriangle_decode_encode :
    ∀ h : BHist,
      subjectReductionRouteTriangleDecodeBHist
          (subjectReductionRouteTriangleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subjectReductionRouteTriangleFields :
    SubjectReductionRouteTriangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionRouteTriangleUp.mk B E O L H C P N =>
      [B, E, O, L, H, C, P, N]

def subjectReductionRouteTriangleToEventFlow :
    SubjectReductionRouteTriangleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (subjectReductionRouteTriangleFields x).map subjectReductionRouteTriangleEncodeBHist

private def subjectReductionRouteTriangleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subjectReductionRouteTriangleEventAt index rest

def subjectReductionRouteTriangleFromEventFlow
    (ef : EventFlow) : Option SubjectReductionRouteTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SubjectReductionRouteTriangleUp.mk
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 0 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 1 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 2 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 3 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 4 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 5 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 6 ef))
      (subjectReductionRouteTriangleDecodeBHist (subjectReductionRouteTriangleEventAt 7 ef)))

private theorem subjectReductionRouteTriangle_round_trip :
    ∀ x : SubjectReductionRouteTriangleUp,
      subjectReductionRouteTriangleFromEventFlow
          (subjectReductionRouteTriangleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E O L H C P N =>
      change
        some
          (SubjectReductionRouteTriangleUp.mk
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist B))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist E))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist O))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist L))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist H))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist C))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist P))
            (subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist N))) =
          some (SubjectReductionRouteTriangleUp.mk B E O L H C P N)
      rw [subjectReductionRouteTriangle_decode_encode B,
        subjectReductionRouteTriangle_decode_encode E,
        subjectReductionRouteTriangle_decode_encode O,
        subjectReductionRouteTriangle_decode_encode L,
        subjectReductionRouteTriangle_decode_encode H,
        subjectReductionRouteTriangle_decode_encode C,
        subjectReductionRouteTriangle_decode_encode P,
        subjectReductionRouteTriangle_decode_encode N]

private theorem subjectReductionRouteTriangleToEventFlow_injective
    {x y : SubjectReductionRouteTriangleUp} :
    subjectReductionRouteTriangleToEventFlow x = subjectReductionRouteTriangleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionRouteTriangleFromEventFlow
          (subjectReductionRouteTriangleToEventFlow x) =
        subjectReductionRouteTriangleFromEventFlow
          (subjectReductionRouteTriangleToEventFlow y) :=
    congrArg subjectReductionRouteTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionRouteTriangle_round_trip x).symm
      (Eq.trans hread (subjectReductionRouteTriangle_round_trip y)))

private theorem subjectReductionRouteTriangle_fields_faithful :
    ∀ x y : SubjectReductionRouteTriangleUp,
      subjectReductionRouteTriangleFields x = subjectReductionRouteTriangleFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ E₁ O₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ E₂ O₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance subjectReductionRouteTriangleBHistCarrier :
    BHistCarrier SubjectReductionRouteTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionRouteTriangleToEventFlow
  fromEventFlow := subjectReductionRouteTriangleFromEventFlow

instance subjectReductionRouteTriangleChapterTasteGate :
    ChapterTasteGate SubjectReductionRouteTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionRouteTriangleFromEventFlow
          (subjectReductionRouteTriangleToEventFlow x) =
        some x
    exact subjectReductionRouteTriangle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionRouteTriangleToEventFlow_injective heq)

instance subjectReductionRouteTriangleFieldFaithful :
    FieldFaithful SubjectReductionRouteTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subjectReductionRouteTriangleFields
  field_faithful := subjectReductionRouteTriangle_fields_faithful

theorem SubjectReductionRouteTriangleTasteGate_single_carrier_alignment :
    subjectReductionRouteTriangleEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      subjectReductionRouteTriangleEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ h : BHist,
          subjectReductionRouteTriangleDecodeBHist
              (subjectReductionRouteTriangleEncodeBHist h) =
            h) ∧
          Nonempty (BHistCarrier SubjectReductionRouteTriangleUp) ∧
            Nonempty (ChapterTasteGate SubjectReductionRouteTriangleUp) ∧
              Nonempty (FieldFaithful SubjectReductionRouteTriangleUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨rfl, rfl, subjectReductionRouteTriangle_decode_encode,
      ⟨subjectReductionRouteTriangleBHistCarrier⟩,
      ⟨subjectReductionRouteTriangleChapterTasteGate⟩,
      ⟨subjectReductionRouteTriangleFieldFaithful⟩⟩

end BEDC.Derived.SubjectReductionRouteTriangleUp
