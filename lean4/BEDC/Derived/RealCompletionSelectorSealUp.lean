import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
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

inductive RealCompletionSelectorSealUp : Type where
  | mk :
      (budget window readback limit endpoint transport continuation provenance name : BHist) →
      RealCompletionSelectorSealUp
  deriving DecidableEq

def realCompletionSelectorSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionSelectorSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionSelectorSealEncodeBHist h

def realCompletionSelectorSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionSelectorSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionSelectorSealDecodeBHist tail)

private theorem realCompletionSelectorSeal_decode_encode_bhist :
    ∀ h : BHist,
      realCompletionSelectorSealDecodeBHist
        (realCompletionSelectorSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletionSelectorSealToEventFlow : RealCompletionSelectorSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport
      continuation provenance name =>
      [[BMark.b0],
        realCompletionSelectorSealEncodeBHist budget,
        [BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist limit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletionSelectorSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletionSelectorSealEncodeBHist name]

def realCompletionSelectorSealFromEventFlow : EventFlow → Option RealCompletionSelectorSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: budget :: _tag1 :: window :: _tag2 :: readback :: _tag3 :: limit ::
      _tag4 :: endpoint :: _tag5 :: transport :: _tag6 :: continuation :: _tag7 ::
      provenance :: _tag8 :: name :: [] =>
      some
        (RealCompletionSelectorSealUp.mk
          (realCompletionSelectorSealDecodeBHist budget)
          (realCompletionSelectorSealDecodeBHist window)
          (realCompletionSelectorSealDecodeBHist readback)
          (realCompletionSelectorSealDecodeBHist limit)
          (realCompletionSelectorSealDecodeBHist endpoint)
          (realCompletionSelectorSealDecodeBHist transport)
          (realCompletionSelectorSealDecodeBHist continuation)
          (realCompletionSelectorSealDecodeBHist provenance)
          (realCompletionSelectorSealDecodeBHist name))
  | _ => none

private theorem realCompletionSelectorSeal_round_trip :
    ∀ x : RealCompletionSelectorSealUp,
      realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk budget window readback limit endpoint transport continuation provenance name =>
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
              (realCompletionSelectorSealEncodeBHist continuation))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist provenance))
            (realCompletionSelectorSealDecodeBHist
              (realCompletionSelectorSealEncodeBHist name))) =
          some
            (RealCompletionSelectorSealUp.mk budget window readback limit endpoint transport
              continuation provenance name)
      rw [realCompletionSelectorSeal_decode_encode_bhist budget,
        realCompletionSelectorSeal_decode_encode_bhist window,
        realCompletionSelectorSeal_decode_encode_bhist readback,
        realCompletionSelectorSeal_decode_encode_bhist limit,
        realCompletionSelectorSeal_decode_encode_bhist endpoint,
        realCompletionSelectorSeal_decode_encode_bhist transport,
        realCompletionSelectorSeal_decode_encode_bhist continuation,
        realCompletionSelectorSeal_decode_encode_bhist provenance,
        realCompletionSelectorSeal_decode_encode_bhist name]

private theorem realCompletionSelectorSealToEventFlow_injective
    {x y : RealCompletionSelectorSealUp} :
    realCompletionSelectorSealToEventFlow x = realCompletionSelectorSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
        realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow y) :=
    congrArg realCompletionSelectorSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionSelectorSeal_round_trip x).symm
      (Eq.trans hread (realCompletionSelectorSeal_round_trip y)))

instance realCompletionSelectorSealBHistCarrier : BHistCarrier RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionSelectorSealToEventFlow
  fromEventFlow := realCompletionSelectorSealFromEventFlow

instance realCompletionSelectorSealChapterTasteGate :
    ChapterTasteGate RealCompletionSelectorSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionSelectorSealFromEventFlow (realCompletionSelectorSealToEventFlow x) =
      some x
    exact realCompletionSelectorSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionSelectorSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCompletionSelectorSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionSelectorSealChapterTasteGate

theorem RealCompletionSelectorSealCarrier_nonescape [AskSetup] [PackageSetup]
    {b w r l e h c p n structuralRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      Cont e h structuralRead ->
        Cont structuralRead c terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory b ∧ UnaryHistory w ∧ UnaryHistory r ∧ UnaryHistory l ∧
              UnaryHistory e ∧ UnaryHistory structuralRead ∧ UnaryHistory terminalRead ∧
                Cont b w r ∧ Cont r l e ∧ Cont e h structuralRead ∧
                  Cont structuralRead c terminalRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle terminalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame
  intro carrier endpointStructural structuralTerminal terminalPkg
  rcases carrier with
    ⟨bUnary, wUnary, rUnary, lUnary, eUnary, hUnary, cUnary, _pUnary, _nUnary,
      bWindowReadback, readbackLimitEndpoint, provenancePkg, hName⟩
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed eUnary hUnary endpointStructural
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed structuralUnary cUnary structuralTerminal
  exact
    ⟨bUnary, wUnary, rUnary, lUnary, eUnary, structuralUnary, terminalUnary,
      bWindowReadback, readbackLimitEndpoint, endpointStructural, structuralTerminal,
      provenancePkg, terminalPkg, hName⟩

end BEDC.Derived.RealCompletionSelectorSealUp
