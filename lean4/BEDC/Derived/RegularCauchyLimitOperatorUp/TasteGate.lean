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

namespace BEDC.Derived.RegularCauchyLimitOperatorUp

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

inductive RegularCauchyLimitOperatorUp : Type where
  | mk
      (modulus tail windows readback dyadic handoff sealRow transport replay provenance localName
        exported : BHist) :
      RegularCauchyLimitOperatorUp
  deriving DecidableEq

def regularCauchyLimitOperatorFields :
    RegularCauchyLimitOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLimitOperatorUp.mk modulus tail windows readback dyadic handoff sealRow transport
      replay provenance localName exported =>
      [modulus, tail, windows, readback, dyadic, handoff, sealRow, transport, replay, provenance,
        localName, exported]

def regularCauchyLimitOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLimitOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLimitOperatorEncodeBHist h

def regularCauchyLimitOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLimitOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLimitOperatorDecodeBHist tail)

private theorem regularCauchyLimitOperator_decode_encode :
    ∀ h : BHist,
      regularCauchyLimitOperatorDecodeBHist (regularCauchyLimitOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLimitOperatorToEventFlow :
    RegularCauchyLimitOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyLimitOperatorFields x).map regularCauchyLimitOperatorEncodeBHist

def regularCauchyLimitOperatorFromEventFlow :
    EventFlow → Option RegularCauchyLimitOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | modulus :: tail :: windows :: readback :: dyadic :: handoff :: sealRow :: transport ::
      replay :: provenance :: localName :: exported :: [] =>
      some
        (RegularCauchyLimitOperatorUp.mk
          (regularCauchyLimitOperatorDecodeBHist modulus)
          (regularCauchyLimitOperatorDecodeBHist tail)
          (regularCauchyLimitOperatorDecodeBHist windows)
          (regularCauchyLimitOperatorDecodeBHist readback)
          (regularCauchyLimitOperatorDecodeBHist dyadic)
          (regularCauchyLimitOperatorDecodeBHist handoff)
          (regularCauchyLimitOperatorDecodeBHist sealRow)
          (regularCauchyLimitOperatorDecodeBHist transport)
          (regularCauchyLimitOperatorDecodeBHist replay)
          (regularCauchyLimitOperatorDecodeBHist provenance)
          (regularCauchyLimitOperatorDecodeBHist localName)
          (regularCauchyLimitOperatorDecodeBHist exported))
  | _ => none

private theorem regularCauchyLimitOperator_round_trip :
    ∀ x : RegularCauchyLimitOperatorUp,
      regularCauchyLimitOperatorFromEventFlow
        (regularCauchyLimitOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulus tail windows readback dyadic handoff sealRow transport replay provenance localName
      exported =>
      change
        some
            (RegularCauchyLimitOperatorUp.mk
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist modulus))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist tail))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist windows))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist readback))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist dyadic))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist handoff))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist sealRow))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist transport))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist replay))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist provenance))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist localName))
              (regularCauchyLimitOperatorDecodeBHist
                (regularCauchyLimitOperatorEncodeBHist exported))) =
          some
            (RegularCauchyLimitOperatorUp.mk modulus tail windows readback dyadic handoff sealRow
              transport replay provenance localName exported)
      rw [regularCauchyLimitOperator_decode_encode modulus,
        regularCauchyLimitOperator_decode_encode tail,
        regularCauchyLimitOperator_decode_encode windows,
        regularCauchyLimitOperator_decode_encode readback,
        regularCauchyLimitOperator_decode_encode dyadic,
        regularCauchyLimitOperator_decode_encode handoff,
        regularCauchyLimitOperator_decode_encode sealRow,
        regularCauchyLimitOperator_decode_encode transport,
        regularCauchyLimitOperator_decode_encode replay,
        regularCauchyLimitOperator_decode_encode provenance,
        regularCauchyLimitOperator_decode_encode localName,
        regularCauchyLimitOperator_decode_encode exported]

private theorem regularCauchyLimitOperatorToEventFlow_injective
    {x y : RegularCauchyLimitOperatorUp} :
    regularCauchyLimitOperatorToEventFlow x =
        regularCauchyLimitOperatorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLimitOperatorFromEventFlow (regularCauchyLimitOperatorToEventFlow x) =
        regularCauchyLimitOperatorFromEventFlow (regularCauchyLimitOperatorToEventFlow y) :=
    congrArg regularCauchyLimitOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLimitOperator_round_trip x).symm
      (Eq.trans hread (regularCauchyLimitOperator_round_trip y)))

instance regularCauchyLimitOperatorBHistCarrier :
    BHistCarrier RegularCauchyLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLimitOperatorToEventFlow
  fromEventFlow := regularCauchyLimitOperatorFromEventFlow

instance regularCauchyLimitOperatorChapterTasteGate :
    ChapterTasteGate RegularCauchyLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLimitOperatorFromEventFlow
        (regularCauchyLimitOperatorToEventFlow x) = some x
    exact regularCauchyLimitOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLimitOperatorToEventFlow_injective heq)

instance regularCauchyLimitOperatorNontrivial :
    Nontrivial RegularCauchyLimitOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLimitOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyLimitOperatorUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLimitOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLimitOperatorChapterTasteGate

def RegularCauchyLimitOperatorPacket [AskSetup] [PackageSetup]
    (modulus tail windows readback dyadic handoff sealRow transport replay provenance localName
      exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory modulus ∧ UnaryHistory tail ∧ UnaryHistory windows ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory handoff ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ UnaryHistory exported ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame exported sealRow

theorem RegularCauchyLimitOperatorNameCertObligations [AskSetup] [PackageSetup]
    {modulus tail windows readback dyadic handoff sealRow transport replay provenance localName
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitOperatorPacket modulus tail windows readback dyadic handoff sealRow transport
        replay provenance localName exported bundle pkg →
      Cont modulus tail windows →
        Cont windows readback dyadic →
          Cont handoff sealRow exported →
            SemanticNameCert
                (fun row : BHist => hsame row exported ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row modulus ∨ hsame row tail ∨ hsame row windows ∨
                    hsame row readback ∨ hsame row dyadic ∨ hsame row handoff ∨ hsame row sealRow)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    hsame row exported)
                hsame ∧
              UnaryHistory exported := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusTailWindows windowsReadbackDyadic handoffSealExported
  obtain ⟨_modulusUnary, _tailUnary, _windowsUnary, _readbackUnary, _dyadicUnary,
    _handoffUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, _replayRoute, provenancePkg, localNamePkg,
    exportedSeal⟩ := packet
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row tail ∨ hsame row windows ∨ hsame row readback ∨
              hsame row dyadic ∨ hsame row handoff ∨ hsame row sealRow)
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_trans source.left exportedSeal))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact ⟨cert, exportedUnary⟩

end BEDC.Derived.RegularCauchyLimitOperatorUp
