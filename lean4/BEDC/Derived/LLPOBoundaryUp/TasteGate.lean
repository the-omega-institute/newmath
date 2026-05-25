import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LLPOBoundaryUp

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

inductive LLPOBoundaryUp : Type where
  | mk
      (leftZero rightZero schedule readback dyadic realSeal refusal transport replay
        provenance nameRow : BHist) : LLPOBoundaryUp
  deriving DecidableEq

def llpoBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: llpoBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: llpoBoundaryEncodeBHist h

def llpoBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (llpoBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (llpoBoundaryDecodeBHist tail)

private theorem llpoBoundaryDecode_encode_bhist :
    ∀ h : BHist, llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def llpoBoundaryFields : LLPOBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LLPOBoundaryUp.mk leftZero rightZero schedule readback dyadic realSeal refusal transport
      replay provenance nameRow =>
      [leftZero, rightZero, schedule, readback, dyadic, realSeal, refusal, transport, replay,
        provenance, nameRow]

def llpoBoundaryToEventFlow : LLPOBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (llpoBoundaryFields x).map llpoBoundaryEncodeBHist

private def llpoBoundaryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => llpoBoundaryEventAt index rest

def llpoBoundaryFromEventFlow (ef : EventFlow) : Option LLPOBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LLPOBoundaryUp.mk
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 0 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 1 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 2 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 3 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 4 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 5 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 6 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 7 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 8 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 9 ef))
      (llpoBoundaryDecodeBHist (llpoBoundaryEventAt 10 ef)))

private theorem llpoBoundary_round_trip (x : LLPOBoundaryUp) :
    llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk leftZero rightZero schedule readback dyadic realSeal refusal transport replay
      provenance nameRow =>
      change
        some
          (LLPOBoundaryUp.mk
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist leftZero))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist rightZero))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist schedule))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist readback))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist dyadic))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist realSeal))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist refusal))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist transport))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist replay))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist provenance))
            (llpoBoundaryDecodeBHist (llpoBoundaryEncodeBHist nameRow))) =
          some
            (LLPOBoundaryUp.mk leftZero rightZero schedule readback dyadic realSeal refusal
              transport replay provenance nameRow)
      rw [llpoBoundaryDecode_encode_bhist leftZero,
        llpoBoundaryDecode_encode_bhist rightZero,
        llpoBoundaryDecode_encode_bhist schedule,
        llpoBoundaryDecode_encode_bhist readback,
        llpoBoundaryDecode_encode_bhist dyadic,
        llpoBoundaryDecode_encode_bhist realSeal,
        llpoBoundaryDecode_encode_bhist refusal,
        llpoBoundaryDecode_encode_bhist transport,
        llpoBoundaryDecode_encode_bhist replay,
        llpoBoundaryDecode_encode_bhist provenance,
        llpoBoundaryDecode_encode_bhist nameRow]

private theorem llpoBoundaryToEventFlow_injective {x y : LLPOBoundaryUp} :
    llpoBoundaryToEventFlow x = llpoBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) =
        llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow y) :=
    congrArg llpoBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (llpoBoundary_round_trip x).symm
      (Eq.trans hread (llpoBoundary_round_trip y)))

instance llpoBoundaryBHistCarrier : BHistCarrier LLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := llpoBoundaryToEventFlow
  fromEventFlow := llpoBoundaryFromEventFlow

instance llpoBoundaryChapterTasteGate : ChapterTasteGate LLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change llpoBoundaryFromEventFlow (llpoBoundaryToEventFlow x) = some x
    exact llpoBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (llpoBoundaryToEventFlow_injective heq)

instance llpoBoundaryNontrivial : Nontrivial LLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LLPOBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LLPOBoundaryUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LLPOBoundaryCarrier [AskSetup] [PackageSetup]
    (leftZero rightZero schedule readback dyadic realSeal refusal transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftZero ∧ UnaryHistory rightZero ∧ UnaryHistory schedule ∧
    UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
      UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont schedule readback dyadic ∧
          Cont dyadic realSeal refusal ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧ hsame nameRow refusal

theorem LLPOBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {leftZero rightZero schedule readback dyadic realSeal refusal transport replay provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LLPOBoundaryCarrier leftZero rightZero schedule readback dyadic realSeal refusal transport
        replay provenance nameRow bundle pkg ->
      Cont schedule readback dyadic ->
        Cont dyadic realSeal refusal ->
          PkgSig bundle nameRow pkg ->
            SemanticNameCert
              (fun row : BHist =>
                LLPOBoundaryCarrier leftZero rightZero schedule readback dyadic realSeal
                    refusal transport replay provenance nameRow bundle pkg ∧
                  hsame row nameRow)
              (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
              (fun row : BHist => hsame row refusal ∧ PkgSig bundle nameRow pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro carrier _scheduleReadbackDyadic _dyadicRealRefusal namePkg
  have carrierPacket :
      LLPOBoundaryCarrier leftZero rightZero schedule readback dyadic realSeal refusal
        transport replay provenance nameRow bundle pkg :=
    carrier
  obtain ⟨_leftUnary, _rightUnary, _scheduleUnary, _readbackUnary, _dyadicUnary,
    _realUnary, _refusalUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
    _scheduleReadbackDyadic, _dyadicRealRefusal, _transportReplayProvenance,
    _provenancePkg, _namePkg, sameNameRefusal⟩ := carrier
  exact {
    core := {
      carrier_inhabited := by
        exact Exists.intro nameRow (And.intro carrierPacket (hsame_refl nameRow))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.right (unary_transport nameUnary (hsame_symm source.right))
    ledger_sound := by
      intro _row source
      exact And.intro (hsame_trans source.right sameNameRefusal) namePkg
  }

end BEDC.Derived.LLPOBoundaryUp
