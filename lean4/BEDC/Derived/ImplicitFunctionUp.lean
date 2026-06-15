import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ImplicitFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ImplicitFunctionCarrier [AskSetup] [PackageSetup]
    (equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory equation ∧ UnaryHistory base ∧ UnaryHistory derivative ∧
    UnaryHistory linear ∧ UnaryHistory matrix ∧ UnaryHistory picard ∧ UnaryHistory graph ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont equation base derivative ∧
          Cont derivative linear matrix ∧ Cont matrix picard graph ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem ImplicitFunctionRootEquationCarrier [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName graphRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionCarrier equation base derivative linear matrix picard graph sealRow transport
        replay provenance localName bundle pkg →
      Cont picard graph graphRead →
        PkgSig bundle graphRead pkg →
          UnaryHistory equation ∧ UnaryHistory base ∧ UnaryHistory derivative ∧
            UnaryHistory linear ∧ UnaryHistory matrix ∧ UnaryHistory picard ∧
              UnaryHistory graph ∧ UnaryHistory sealRow ∧ UnaryHistory graphRead ∧
                Cont equation base derivative ∧ Cont derivative linear matrix ∧
                  Cont matrix picard graph ∧ Cont picard graph graphRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle graphRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier picardGraphRead graphReadPkg
  obtain
    ⟨equationUnary, baseUnary, derivativeUnary, linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, equationBaseDerivative, derivativeLinearMatrix, matrixPicardGraph,
      _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed picardUnary graphUnary picardGraphRead
  exact
    ⟨equationUnary, baseUnary, derivativeUnary, linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, graphReadUnary, equationBaseDerivative, derivativeLinearMatrix,
      matrixPicardGraph, picardGraphRead, localNamePkg, graphReadPkg⟩

end BEDC.Derived.ImplicitFunctionUp
