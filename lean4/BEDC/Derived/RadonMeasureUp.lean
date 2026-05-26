import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RadonMeasureUp : Type :=
  Unit

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

end RadonMeasureUp

end BEDC.Derived
