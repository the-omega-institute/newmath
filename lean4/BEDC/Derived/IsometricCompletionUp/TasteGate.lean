import BEDC.Derived.IsometricCompletionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IsometricCompletionUp

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

def IsometricCompletionCarrier [AskSetup] [PackageSetup]
    (metric completion separated filter net uniform embedding realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory metric ∧ UnaryHistory completion ∧ UnaryHistory separated ∧
    UnaryHistory filter ∧ UnaryHistory net ∧ UnaryHistory uniform ∧
      UnaryHistory embedding ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          hsame transport (append separated embedding) ∧
            Cont filter net uniform ∧ Cont metric uniform replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

def isometricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: isometricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: isometricCompletionEncodeBHist h

def isometricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (isometricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (isometricCompletionDecodeBHist tail)

private theorem isometricCompletion_decode_encode :
    ∀ h : BHist, isometricCompletionDecodeBHist (isometricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def isometricCompletionFields : BEDC.Derived.IsometricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.IsometricCompletionUp.mk m k s f t u e r h c p n =>
      [m, k, s, f, t, u, e, r, h, c, p, n]

def isometricCompletionToEventFlow : BEDC.Derived.IsometricCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (isometricCompletionFields x).map isometricCompletionEncodeBHist

private def isometricCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => isometricCompletionEventAtDefault index rest

def isometricCompletionFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.IsometricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.IsometricCompletionUp.mk
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 0 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 1 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 2 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 3 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 4 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 5 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 6 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 7 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 8 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 9 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 10 ef))
      (isometricCompletionDecodeBHist (isometricCompletionEventAtDefault 11 ef)))

private theorem isometricCompletion_round_trip :
    ∀ x : BEDC.Derived.IsometricCompletionUp,
      isometricCompletionFromEventFlow (isometricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk m k s f t u e r h c p n =>
      change
        some
          (BEDC.Derived.IsometricCompletionUp.mk
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist m))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist k))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist s))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist f))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist t))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist u))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist e))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist r))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist h))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist c))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist p))
            (isometricCompletionDecodeBHist (isometricCompletionEncodeBHist n))) =
          some (BEDC.Derived.IsometricCompletionUp.mk m k s f t u e r h c p n)
      rw [isometricCompletion_decode_encode m, isometricCompletion_decode_encode k,
        isometricCompletion_decode_encode s, isometricCompletion_decode_encode f,
        isometricCompletion_decode_encode t, isometricCompletion_decode_encode u,
        isometricCompletion_decode_encode e, isometricCompletion_decode_encode r,
        isometricCompletion_decode_encode h, isometricCompletion_decode_encode c,
        isometricCompletion_decode_encode p, isometricCompletion_decode_encode n]

private theorem isometricCompletionToEventFlow_injective
    {x y : BEDC.Derived.IsometricCompletionUp} :
    isometricCompletionToEventFlow x = isometricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      isometricCompletionFromEventFlow (isometricCompletionToEventFlow x) =
        isometricCompletionFromEventFlow (isometricCompletionToEventFlow y) :=
    congrArg isometricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (isometricCompletion_round_trip x).symm
      (Eq.trans hread (isometricCompletion_round_trip y)))

instance isometricCompletionBHistCarrier :
    BHistCarrier BEDC.Derived.IsometricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := isometricCompletionToEventFlow
  fromEventFlow := isometricCompletionFromEventFlow

instance isometricCompletionChapterTasteGate :
    ChapterTasteGate BEDC.Derived.IsometricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change isometricCompletionFromEventFlow (isometricCompletionToEventFlow x) = some x
    exact isometricCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (isometricCompletionToEventFlow_injective heq)

instance isometricCompletionNontrivial :
    Nontrivial BEDC.Derived.IsometricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.IsometricCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BEDC.Derived.IsometricCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.IsometricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  isometricCompletionChapterTasteGate

theorem IsometricCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric completion separated filter net uniform embedding realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IsometricCompletionCarrier metric completion separated filter net uniform embedding realSeal
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          IsometricCompletionCarrier metric completion separated filter net uniform embedding
            realSeal transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  let carrierWitness := carrier
  obtain
    ⟨_metricUnary, _completionUnary, _separatedUnary, _filterUnary, _netUnary,
      _uniformUnary, _embeddingUnary, _realSealUnary, _transportUnary, _replayUnary,
      provenanceUnary, localNameUnary, _transportSame, _filterNetRoute, _metricReplayRoute,
      provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro carrierWitness (hsame_refl localName))
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
      exact ⟨source.right, unary_transport localNameUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.right⟩
  }

end BEDC.Derived.IsometricCompletionUp
