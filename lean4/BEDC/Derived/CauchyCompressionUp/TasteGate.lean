import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompressionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompressionUp : Type where
  | mk (M S D Q F E H C0 P N : BHist) : CauchyCompressionUp
  deriving DecidableEq

def cauchyCompressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompressionEncodeBHist h

def cauchyCompressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompressionDecodeBHist tail)

private theorem CauchyCompressionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompressionToEventFlow : CauchyCompressionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompressionUp.mk M S D Q F E H C0 P N =>
      [[BMark.b0],
        cauchyCompressionEncodeBHist M,
        [BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyCompressionEncodeBHist C0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyCompressionEncodeBHist N]

private def cauchyCompressionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompressionEventAtDefault index rest

def cauchyCompressionFromEventFlow (ef : EventFlow) : Option CauchyCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompressionUp.mk
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 1 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 3 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 5 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 7 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 9 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 11 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 13 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 15 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 17 ef))
      (cauchyCompressionDecodeBHist (cauchyCompressionEventAtDefault 19 ef)))

private theorem CauchyCompressionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompressionUp,
      cauchyCompressionFromEventFlow (cauchyCompressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D Q F E H C0 P N =>
      change
        some
          (CauchyCompressionUp.mk
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist M))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist S))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist D))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist Q))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist F))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist E))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist H))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist C0))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist P))
            (cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist N))) =
          some (CauchyCompressionUp.mk M S D Q F E H C0 P N)
      rw [CauchyCompressionTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode F,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode C0,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompressionTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompressionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompressionUp} :
    cauchyCompressionToEventFlow x = cauchyCompressionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompressionFromEventFlow (cauchyCompressionToEventFlow x) =
        cauchyCompressionFromEventFlow (cauchyCompressionToEventFlow y) :=
    congrArg cauchyCompressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompressionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCompressionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompressionBHistCarrier : BHistCarrier CauchyCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompressionToEventFlow
  fromEventFlow := cauchyCompressionFromEventFlow

instance cauchyCompressionChapterTasteGate : ChapterTasteGate CauchyCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCompressionFromEventFlow (cauchyCompressionToEventFlow x) = some x
    exact CauchyCompressionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompressionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompressionChapterTasteGate

theorem CauchyCompressionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCompressionDecodeBHist (cauchyCompressionEncodeBHist h) = h) ∧
      (∀ x : CauchyCompressionUp,
        cauchyCompressionFromEventFlow (cauchyCompressionToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompressionUp,
          cauchyCompressionToEventFlow x = cauchyCompressionToEventFlow y → x = y) ∧
          cauchyCompressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompressionTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompressionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyCompressionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

def CauchyCompressionCarrier [AskSetup] [PackageSetup]
    (modulus windows tolerance readback fast sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory fast ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont modulus windows tolerance ∧
          Cont tolerance readback fast ∧ Cont fast sealRow replay ∧
            PkgSig bundle name pkg ∧ hsame name (append provenance sealRow)

theorem CauchyCompressionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {modulus windows tolerance readback fast sealRow transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompressionCarrier modulus windows tolerance readback fast sealRow transport replay
        provenance name bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist => hsame row name ∧ Cont fast sealRow replay)
          (fun _row : BHist => PkgSig bundle name pkg ∧ hsame name (append provenance sealRow))
          hsame ∧
        UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
          UnaryHistory readback ∧ UnaryHistory fast ∧ UnaryHistory sealRow ∧
            Cont modulus windows tolerance ∧ Cont tolerance readback fast ∧
              Cont fast sealRow replay ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨modulusUnary, windowsUnary, toleranceUnary, readbackUnary, fastUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, nameUnary, modulusWindowsTolerance,
    toleranceReadbackFast, fastSealReplay, namePkg, nameAppend⟩ := carrier
  have sourceAtName :
      (fun row : BHist => hsame row name ∧ UnaryHistory row) name :=
    And.intro (hsame_refl name) nameUnary
  have cert :
      SemanticNameCert (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist => hsame row name ∧ Cont fast sealRow replay)
          (fun _row : BHist => PkgSig bundle name pkg ∧ hsame name (append provenance sealRow))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name sourceAtName
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
      exact And.intro source.left fastSealReplay
    ledger_sound := by
      intro _row _source
      exact And.intro namePkg nameAppend
  }
  exact
    ⟨cert, modulusUnary, windowsUnary, toleranceUnary, readbackUnary, fastUnary, sealUnary,
      modulusWindowsTolerance, toleranceReadbackFast, fastSealReplay, namePkg⟩

end BEDC.Derived.CauchyCompressionUp
