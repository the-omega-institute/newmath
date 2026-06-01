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

namespace BEDC.Derived.DyadicMeshCompositionUp

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

inductive DyadicMeshCompositionUp : Type where
  | mk
      (mesh0 mesh1 refinement dyadic transport replay provenance localName exported : BHist) :
      DyadicMeshCompositionUp
  deriving DecidableEq

def dyadicMeshCompositionPacketFields :
    DyadicMeshCompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMeshCompositionUp.mk mesh0 mesh1 refinement dyadic transport replay provenance
      localName exported =>
      [mesh0, mesh1, refinement, dyadic, transport, replay, provenance, localName, exported]

def dyadicMeshCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMeshCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMeshCompositionEncodeBHist h

def dyadicMeshCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMeshCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMeshCompositionDecodeBHist tail)

private theorem dyadicMeshComposition_decode_encode :
    ∀ h : BHist, dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMeshCompositionToEventFlow : DyadicMeshCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicMeshCompositionPacketFields x).map dyadicMeshCompositionEncodeBHist

def dyadicMeshCompositionFromEventFlow : EventFlow → Option DyadicMeshCompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | mesh0 :: mesh1 :: refinement :: dyadic :: transport :: replay :: provenance ::
      localName :: exported :: [] =>
      some
        (DyadicMeshCompositionUp.mk
          (dyadicMeshCompositionDecodeBHist mesh0)
          (dyadicMeshCompositionDecodeBHist mesh1)
          (dyadicMeshCompositionDecodeBHist refinement)
          (dyadicMeshCompositionDecodeBHist dyadic)
          (dyadicMeshCompositionDecodeBHist transport)
          (dyadicMeshCompositionDecodeBHist replay)
          (dyadicMeshCompositionDecodeBHist provenance)
          (dyadicMeshCompositionDecodeBHist localName)
          (dyadicMeshCompositionDecodeBHist exported))
  | _ => none

private theorem dyadicMeshComposition_round_trip :
    ∀ x : DyadicMeshCompositionUp,
      dyadicMeshCompositionFromEventFlow (dyadicMeshCompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk mesh0 mesh1 refinement dyadic transport replay provenance localName exported =>
      change
        some
            (DyadicMeshCompositionUp.mk
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist mesh0))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist mesh1))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist refinement))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist dyadic))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist transport))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist replay))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist provenance))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist localName))
              (dyadicMeshCompositionDecodeBHist (dyadicMeshCompositionEncodeBHist exported))) =
          some
            (DyadicMeshCompositionUp.mk mesh0 mesh1 refinement dyadic transport replay
              provenance localName exported)
      rw [dyadicMeshComposition_decode_encode mesh0, dyadicMeshComposition_decode_encode mesh1,
        dyadicMeshComposition_decode_encode refinement, dyadicMeshComposition_decode_encode dyadic,
        dyadicMeshComposition_decode_encode transport, dyadicMeshComposition_decode_encode replay,
        dyadicMeshComposition_decode_encode provenance,
        dyadicMeshComposition_decode_encode localName,
        dyadicMeshComposition_decode_encode exported]

private theorem dyadicMeshCompositionToEventFlow_injective {x y : DyadicMeshCompositionUp} :
    dyadicMeshCompositionToEventFlow x = dyadicMeshCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMeshCompositionFromEventFlow (dyadicMeshCompositionToEventFlow x) =
        dyadicMeshCompositionFromEventFlow (dyadicMeshCompositionToEventFlow y) :=
    congrArg dyadicMeshCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicMeshComposition_round_trip x).symm
      (Eq.trans hread (dyadicMeshComposition_round_trip y)))

instance dyadicMeshCompositionBHistCarrier : BHistCarrier DyadicMeshCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMeshCompositionToEventFlow
  fromEventFlow := dyadicMeshCompositionFromEventFlow

instance dyadicMeshCompositionChapterTasteGate :
    ChapterTasteGate DyadicMeshCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMeshCompositionFromEventFlow (dyadicMeshCompositionToEventFlow x) = some x
    exact dyadicMeshComposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicMeshCompositionToEventFlow_injective heq)

instance dyadicMeshCompositionNontrivial : Nontrivial DyadicMeshCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicMeshCompositionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicMeshCompositionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicMeshCompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicMeshCompositionChapterTasteGate

def DyadicMeshCompositionPacket [AskSetup] [PackageSetup]
    (mesh0 mesh1 refinement dyadic transport replay provenance localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory mesh0 ∧ UnaryHistory mesh1 ∧ UnaryHistory refinement ∧
    UnaryHistory dyadic ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ UnaryHistory exported ∧
        Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem DyadicMeshCompositionNameCertObligations [AskSetup] [PackageSetup]
    {mesh0 mesh1 refinement dyadic transport replay provenance localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshCompositionPacket mesh0 mesh1 refinement dyadic transport replay provenance
        localName exported bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mesh0 ∨ hsame row mesh1 ∨ hsame row refinement ∨
              hsame row dyadic ∨ Cont transport replay provenance)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row exported)
          hsame ∧
        UnaryHistory mesh0 ∧ UnaryHistory mesh1 ∧ UnaryHistory refinement ∧
          UnaryHistory dyadic := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨mesh0Unary, mesh1Unary, refinementUnary, dyadicUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, exportedUnary, replayRoute,
    provenancePkg, localNamePkg⟩ := packet
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mesh0 ∨ hsame row mesh1 ∨ hsame row refinement ∨
              hsame row dyadic ∨ Cont transport replay provenance)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row exported)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr replayRoute)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact ⟨cert, mesh0Unary, mesh1Unary, refinementUnary, dyadicUnary⟩

end BEDC.Derived.DyadicMeshCompositionUp
