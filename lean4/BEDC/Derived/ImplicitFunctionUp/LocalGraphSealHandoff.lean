import BEDC.Derived.ImplicitFunctionUp

namespace BEDC.Derived.ImplicitFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ImplicitFunctionLocalGraphSealHandoff [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph sealRow transport replay provenance
      localName graphRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ImplicitFunctionCarrier equation base derivative linear matrix picard graph sealRow transport
        replay provenance localName bundle pkg →
      Cont picard graph graphRead →
        Cont graphRead sealRow sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory derivative ∧ UnaryHistory matrix ∧ UnaryHistory graph ∧
              UnaryHistory graphRead ∧ UnaryHistory sealRead ∧
                Cont derivative linear matrix ∧ Cont matrix picard graph ∧
                  Cont picard graph graphRead ∧ Cont graphRead sealRow sealRead ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier picardGraphRead graphReadSealRead sealReadPkg
  obtain
    ⟨_equationUnary, _baseUnary, derivativeUnary, _linearUnary, matrixUnary, picardUnary,
      graphUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, _equationBaseDerivative, derivativeLinearMatrix, matrixPicardGraph,
      _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed picardUnary graphUnary picardGraphRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed graphReadUnary sealUnary graphReadSealRead
  exact
    ⟨derivativeUnary, matrixUnary, graphUnary, graphReadUnary, sealReadUnary,
      derivativeLinearMatrix, matrixPicardGraph, picardGraphRead, graphReadSealRead,
      localNamePkg, sealReadPkg⟩

end BEDC.Derived.ImplicitFunctionUp
