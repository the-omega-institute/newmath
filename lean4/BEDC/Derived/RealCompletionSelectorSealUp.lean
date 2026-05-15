import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionSelectorSealUp

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

inductive RealCompletionSelectorSealUp : Type where
  | mk :
      (budget window readback limit endpoint transport route provenance name : BHist) →
        RealCompletionSelectorSealUp
  deriving DecidableEq

def realCompletionSelectorSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionSelectorSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionSelectorSealEncodeBHist h

def realCompletionSelectorSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionSelectorSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionSelectorSealDecodeBHist tail)

private theorem realCompletionSelectorSealDecode_encode_bhist :
    ∀ h : BHist,
      realCompletionSelectorSealDecodeBHist
        (realCompletionSelectorSealEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletionSelectorSealToEventFlow :
    RealCompletionSelectorSealUp → EventFlow
  | RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport route
      provenance name =>
      [realCompletionSelectorSealEncodeBHist budget,
        realCompletionSelectorSealEncodeBHist window,
        realCompletionSelectorSealEncodeBHist readback,
        realCompletionSelectorSealEncodeBHist limit,
        realCompletionSelectorSealEncodeBHist endpoint,
        realCompletionSelectorSealEncodeBHist transport,
        realCompletionSelectorSealEncodeBHist route,
        realCompletionSelectorSealEncodeBHist provenance,
        realCompletionSelectorSealEncodeBHist name]

def realCompletionSelectorSealFromEventFlow :
    EventFlow → Option RealCompletionSelectorSealUp
  | [budget, window, readback, limit, endpoint, transport, route, provenance, name] =>
      some
        (RealCompletionSelectorSealUp.mk
          (realCompletionSelectorSealDecodeBHist budget)
          (realCompletionSelectorSealDecodeBHist window)
          (realCompletionSelectorSealDecodeBHist readback)
          (realCompletionSelectorSealDecodeBHist limit)
          (realCompletionSelectorSealDecodeBHist endpoint)
          (realCompletionSelectorSealDecodeBHist transport)
          (realCompletionSelectorSealDecodeBHist route)
          (realCompletionSelectorSealDecodeBHist provenance)
          (realCompletionSelectorSealDecodeBHist name))
  | _ => none

private theorem realCompletionSelectorSeal_round_trip :
    ∀ x : RealCompletionSelectorSealUp,
      realCompletionSelectorSealFromEventFlow
        (realCompletionSelectorSealToEventFlow x) = some x := by
  intro x
  cases x with
  | mk budget window readback limit endpoint transport route provenance name =>
      change
        some
          (RealCompletionSelectorSealUp.mk
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist budget))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist window))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist readback))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist limit))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist endpoint))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist transport))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist route))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist provenance))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist name))) =
          some
            (RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport
              route provenance name)
      rw [realCompletionSelectorSealDecode_encode_bhist budget,
        realCompletionSelectorSealDecode_encode_bhist window,
        realCompletionSelectorSealDecode_encode_bhist readback,
        realCompletionSelectorSealDecode_encode_bhist limit,
        realCompletionSelectorSealDecode_encode_bhist endpoint,
        realCompletionSelectorSealDecode_encode_bhist transport,
        realCompletionSelectorSealDecode_encode_bhist route,
        realCompletionSelectorSealDecode_encode_bhist provenance,
        realCompletionSelectorSealDecode_encode_bhist name]

private theorem realCompletionSelectorSealToEventFlow_injective
    {x y : RealCompletionSelectorSealUp} :
    realCompletionSelectorSealToEventFlow x =
      realCompletionSelectorSealToEventFlow y → x = y := by
  intro heq
  have hread :
      realCompletionSelectorSealFromEventFlow
          (realCompletionSelectorSealToEventFlow x) =
        realCompletionSelectorSealFromEventFlow
          (realCompletionSelectorSealToEventFlow y) :=
    congrArg realCompletionSelectorSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionSelectorSeal_round_trip x).symm
      (Eq.trans hread (realCompletionSelectorSeal_round_trip y)))

instance realCompletionSelectorSealBHistCarrier :
    BHistCarrier RealCompletionSelectorSealUp where
  toEventFlow := realCompletionSelectorSealToEventFlow
  fromEventFlow := realCompletionSelectorSealFromEventFlow

instance realCompletionSelectorSealChapterTasteGate :
    ChapterTasteGate RealCompletionSelectorSealUp where
  round_trip := by
    intro x
    change
      realCompletionSelectorSealFromEventFlow
        (realCompletionSelectorSealToEventFlow x) = some x
    exact realCompletionSelectorSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionSelectorSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCompletionSelectorSealUp :=
  realCompletionSelectorSealChapterTasteGate

def RealCompletionSelectorSealCarrier [AskSetup] [PackageSetup]
    (b w r l e h c p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  UnaryHistory b ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory l ∧
    UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧
      UnaryHistory n ∧ Cont b w r ∧ Cont r l e ∧ PkgSig bundle p pkg ∧ hsame h n

theorem RealCompletionSelectorSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {b w r l e h c p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ∧ hsame row e)
        (fun row : BHist =>
          Cont b w r ∧ Cont r l e ∧ hsame row e ∧ PkgSig bundle p pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle p pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier
  have bUnary : UnaryHistory b := carrier.left
  have wUnary : UnaryHistory w := carrier.right.left
  have rUnary : UnaryHistory r := carrier.right.right.left
  have lUnary : UnaryHistory l := carrier.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.left
  have hUnary : UnaryHistory h := carrier.right.right.right.right.right.left
  have cUnary : UnaryHistory c := carrier.right.right.right.right.right.right.left
  have pUnary : UnaryHistory p := carrier.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory n := carrier.right.right.right.right.right.right.right.right.left
  have bwr : Cont b w r := carrier.right.right.right.right.right.right.right.right.right.left
  have rle : Cont r l e := carrier.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have hn : hsame h n :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro e (And.intro
          ⟨bUnary, wUnary, rUnary, lUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
            bwr, rle, pPkg, hn⟩
          (hsame_refl e))
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
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨bwr, rle, source.right, pPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport eUnary (hsame_symm source.right)) pPkg
  }

end BEDC.Derived.RealCompletionSelectorSealUp
