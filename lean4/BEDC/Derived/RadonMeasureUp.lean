import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RadonMeasureUp : Type where
  | mk (X M O K V D H C P N : BHist) : RadonMeasureUp
  deriving DecidableEq

namespace RadonMeasureUp

def RadonMeasureCarrier [AskSetup] [PackageSetup]
    (X M O K V D H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory O ∧ UnaryHistory K ∧
    UnaryHistory V ∧ UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory N ∧ Cont X M O ∧ Cont O K V ∧ Cont V D C ∧ PkgSig bundle P pkg

theorem RadonMeasureCarrier_compact_regularity_route [AskSetup] [PackageSetup]
    {X M O K V D H C P N compactRead outerRead distributionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RadonMeasureCarrier X M O K V D H C P N bundle pkg →
      Cont X M compactRead →
        Cont compactRead O outerRead →
          Cont outerRead D distributionRead →
            PkgSig bundle distributionRead pkg →
              UnaryHistory X ∧ UnaryHistory M ∧ UnaryHistory O ∧ UnaryHistory D ∧
                UnaryHistory compactRead ∧ UnaryHistory outerRead ∧
                  UnaryHistory distributionRead ∧ Cont X M compactRead ∧
                    Cont compactRead O outerRead ∧ Cont outerRead D distributionRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle distributionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier compactRoute outerRoute distributionRoute distributionPkg
  obtain ⟨xUnary, mUnary, oUnary, _kUnary, _vUnary, dUnary, _hUnary, _cUnary, _nUnary,
    _xmo, _okv, _vdc, pPkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary mUnary compactRoute
  have outerUnary : UnaryHistory outerRead :=
    unary_cont_closed compactUnary oUnary outerRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed outerUnary dUnary distributionRoute
  exact
    ⟨xUnary, mUnary, oUnary, dUnary, compactUnary, outerUnary, distributionUnary,
      compactRoute, outerRoute, distributionRoute, pPkg, distributionPkg⟩

theorem RadonMeasureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X M O K V D H C P N compactRead outerRead variationRead distributionRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RadonMeasureCarrier X M O K V D H C P N bundle pkg ->
      Cont X M compactRead ->
        Cont compactRead O outerRead ->
          Cont outerRead K variationRead ->
            Cont variationRead V distributionRead ->
              Cont distributionRead D replayRead ->
                PkgSig bundle replayRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row M ∨ hsame row O ∨ hsame row K ∨
                          hsame row V ∨ hsame row D ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont X M compactRead ∧
                          Cont compactRead O outerRead ∧ Cont outerRead K variationRead ∧
                            Cont variationRead V distributionRead ∧
                              Cont distributionRead D replayRead ∧
                                PkgSig bundle replayRead pkg)
                      hsame ∧ UnaryHistory compactRead ∧ UnaryHistory outerRead ∧
                    UnaryHistory variationRead ∧ UnaryHistory distributionRead ∧
                      UnaryHistory replayRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: RadonMeasureCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute outerRoute variationRoute distributionRoute replayRoute replayPkg
  obtain ⟨xUnary, mUnary, oUnary, kUnary, vUnary, dUnary, _hUnary, _cUnary, _nUnary,
    _xmo, _okv, _vdc, pPkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary mUnary compactRoute
  have outerUnary : UnaryHistory outerRead :=
    unary_cont_closed compactUnary oUnary outerRoute
  have variationUnary : UnaryHistory variationRead :=
    unary_cont_closed outerUnary kUnary variationRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed variationUnary vUnary distributionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distributionUnary dUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row M ∨ hsame row O ∨ hsame row K ∨
              hsame row V ∨ hsame row D ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X M compactRead ∧ Cont compactRead O outerRead ∧
              Cont outerRead K variationRead ∧ Cont variationRead V distributionRead ∧
                Cont distributionRead D replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      repeat (first | exact sourceRow.left | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, compactRoute, outerRoute, variationRoute, distributionRoute,
          replayRoute, replayPkg⟩
  }
  exact
    ⟨cert, compactUnary, outerUnary, variationUnary, distributionUnary, replayUnary,
      pPkg⟩

end RadonMeasureUp

end BEDC.Derived
