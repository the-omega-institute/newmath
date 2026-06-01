import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpigraphUp

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

inductive EpigraphUp : Type where
  | mk (D V L O H C P N : BHist) : EpigraphUp
  deriving DecidableEq

def epigraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epigraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epigraphEncodeBHist h

def epigraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epigraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epigraphDecodeBHist tail)

private theorem epigraphDecode_encode_bhist :
    ∀ h : BHist, epigraphDecodeBHist (epigraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def epigraphFields : EpigraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EpigraphUp.mk D V L O H C P N => [D, V, L, O, H, C, P, N]

def epigraphToEventFlow : EpigraphUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (epigraphFields x).map epigraphEncodeBHist

def epigraphFromEventFlow : EventFlow → Option EpigraphUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: V :: L :: O :: H :: C :: P :: N :: [] =>
      some
        (EpigraphUp.mk
          (epigraphDecodeBHist D)
          (epigraphDecodeBHist V)
          (epigraphDecodeBHist L)
          (epigraphDecodeBHist O)
          (epigraphDecodeBHist H)
          (epigraphDecodeBHist C)
          (epigraphDecodeBHist P)
          (epigraphDecodeBHist N))
  | _ => none

private theorem epigraph_round_trip :
    ∀ x : EpigraphUp, epigraphFromEventFlow (epigraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D V L O H C P N =>
      simp only [epigraphToEventFlow, epigraphFields, epigraphFromEventFlow, List.map_cons,
        List.map_nil, epigraphDecode_encode_bhist]

private theorem epigraphToEventFlow_injective {x y : EpigraphUp} :
    epigraphToEventFlow x = epigraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epigraphFromEventFlow (epigraphToEventFlow x) =
        epigraphFromEventFlow (epigraphToEventFlow y) :=
    congrArg epigraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (epigraph_round_trip x).symm (Eq.trans hread (epigraph_round_trip y)))

instance epigraphBHistCarrier : BHistCarrier EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epigraphToEventFlow
  fromEventFlow := epigraphFromEventFlow

instance epigraphChapterTasteGate : ChapterTasteGate EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epigraphFromEventFlow (epigraphToEventFlow x) = some x
    exact epigraph_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (epigraphToEventFlow_injective heq)

def EpigraphCarrier [AskSetup] [PackageSetup]
    (D V L O H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory L ∧ UnaryHistory O ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg

theorem EpigraphNameCertObligations [AskSetup] [PackageSetup]
    {D V L O H C P N queryRead comparisonRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphCarrier D V L O H C P N bundle pkg ->
      Cont D V queryRead ->
        Cont L O comparisonRead ->
          Cont queryRead comparisonRead replayRead ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory queryRead ∧ UnaryHistory comparisonRead ∧
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier queryRoute comparisonRoute replayRoute localNamePkg
  obtain ⟨dUnary, vUnary, lUnary, oUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    provenancePkg⟩ := carrier
  have queryUnary : UnaryHistory queryRead :=
    unary_cont_closed dUnary vUnary queryRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed lUnary oUnary comparisonRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed queryUnary comparisonUnary replayRoute
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, queryUnary, comparisonUnary, replayUnary⟩

end BEDC.Derived.EpigraphUp
