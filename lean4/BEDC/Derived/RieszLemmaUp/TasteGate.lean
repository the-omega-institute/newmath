import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszLemmaUp

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

inductive RieszLemmaUp : Type where
  | mk
      (source subspace unit tolerance avoidance distance witness complete transport replay
        provenance name : BHist) :
      RieszLemmaUp
  deriving DecidableEq

def rieszLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszLemmaEncodeBHist h

def rieszLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszLemmaDecodeBHist tail)

private theorem rieszLemmaDecode_encode :
    ∀ h : BHist, rieszLemmaDecodeBHist (rieszLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rieszLemmaFields : RieszLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszLemmaUp.mk source subspace unit tolerance avoidance distance witness complete
      transport replay provenance name =>
      [source, subspace, unit, tolerance, avoidance, distance, witness, complete,
        transport, replay, provenance, name]

def rieszLemmaToEventFlow : RieszLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rieszLemmaFields x).map rieszLemmaEncodeBHist

private def rieszLemmaEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rieszLemmaEventAtDefault index rest

def rieszLemmaFromEventFlow : EventFlow → Option RieszLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RieszLemmaUp.mk
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 0 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 1 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 2 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 3 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 4 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 5 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 6 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 7 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 8 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 9 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 10 ef))
        (rieszLemmaDecodeBHist (rieszLemmaEventAtDefault 11 ef)))

private theorem rieszLemma_round_trip :
    ∀ x : RieszLemmaUp, rieszLemmaFromEventFlow (rieszLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source subspace unit tolerance avoidance distance witness complete transport replay
      provenance name =>
      change
        some
          (RieszLemmaUp.mk
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist source))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist subspace))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist unit))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist tolerance))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist avoidance))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist distance))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist witness))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist complete))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist transport))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist replay))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist provenance))
            (rieszLemmaDecodeBHist (rieszLemmaEncodeBHist name))) =
          some
            (RieszLemmaUp.mk source subspace unit tolerance avoidance distance witness complete
              transport replay provenance name)
      rw [rieszLemmaDecode_encode source, rieszLemmaDecode_encode subspace,
        rieszLemmaDecode_encode unit, rieszLemmaDecode_encode tolerance,
        rieszLemmaDecode_encode avoidance, rieszLemmaDecode_encode distance,
        rieszLemmaDecode_encode witness, rieszLemmaDecode_encode complete,
        rieszLemmaDecode_encode transport, rieszLemmaDecode_encode replay,
        rieszLemmaDecode_encode provenance, rieszLemmaDecode_encode name]

private theorem rieszLemmaToEventFlow_injective {x y : RieszLemmaUp} :
    rieszLemmaToEventFlow x = rieszLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rieszLemmaFromEventFlow (rieszLemmaToEventFlow x) =
        rieszLemmaFromEventFlow (rieszLemmaToEventFlow y) :=
    congrArg rieszLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rieszLemma_round_trip x).symm
      (Eq.trans hread (rieszLemma_round_trip y)))

instance rieszLemmaBHistCarrier : BHistCarrier RieszLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszLemmaToEventFlow
  fromEventFlow := rieszLemmaFromEventFlow

instance rieszLemmaChapterTasteGate : ChapterTasteGate RieszLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszLemmaFromEventFlow (rieszLemmaToEventFlow x) = some x
    exact rieszLemma_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rieszLemmaToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RieszLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rieszLemmaChapterTasteGate

theorem RieszLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, rieszLemmaDecodeBHist (rieszLemmaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RieszLemmaUp) ∧
        Nonempty (ChapterTasteGate RieszLemmaUp) ∧
          rieszLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rieszLemmaDecode_encode,
      ⟨⟨rieszLemmaBHistCarrier⟩, ⟨⟨rieszLemmaChapterTasteGate⟩, rfl⟩⟩⟩

def RieszLemmaCarrier [AskSetup] [PackageSetup]
    (source subspace unit tolerance avoidance distance witness complete transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert
  UnaryHistory source ∧ UnaryHistory subspace ∧ UnaryHistory unit ∧
    UnaryHistory tolerance ∧ UnaryHistory avoidance ∧ UnaryHistory distance ∧
      UnaryHistory witness ∧ UnaryHistory complete ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont source subspace unit ∧ Cont avoidance distance witness ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem RieszLemmaCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source subspace unit tolerance avoidance distance witness complete transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete transport
        replay provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
            transport replay provenance name bundle pkg ∧ hsame row name)
        (fun _row : BHist =>
          RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
            transport replay provenance name bundle pkg ∧ Cont source subspace unit ∧
              Cont avoidance distance witness ∧ Cont transport replay provenance)
        (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro carrierRows
  have carrierWitness := carrierRows
  obtain ⟨_sourceUnary, _subspaceUnary, _unitUnary, _toleranceUnary, _avoidanceUnary,
    _distanceUnary, _witnessUnary, _completeUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, sourceSubspaceUnit, avoidanceDistanceWitness,
    transportReplayProvenance, _provenancePkg, namePkg⟩ := carrierRows
  have sourceAtName :
      RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
          transport replay provenance name bundle pkg ∧ hsame name name :=
    And.intro carrierWitness (hsame_refl name)
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          RieszLemmaCarrier source subspace unit tolerance avoidance distance witness complete
            transport replay provenance name bundle pkg ∧ hsame row name) :=
    Exists.intro name sourceAtName
  exact {
    core := {
      carrier_inhabited := carrierInhabited
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, sourceSubspaceUnit, avoidanceDistanceWitness,
          transportReplayProvenance⟩
    ledger_sound := by
      intro _row sourceRow
      exact And.intro namePkg sourceRow.right
  }

end BEDC.Derived.RieszLemmaUp
