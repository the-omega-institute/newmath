import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_constant_factor_bilinear_seal [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name leftFactor rightFactor bilinearTail realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont sourceA windowA leftFactor ->
        Cont sourceB windowB rightFactor ->
          Cont leftFactor rightFactor bilinearTail ->
            Cont classifier routes realSeal ->
              PkgSig bundle realSeal pkg ->
                UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧
                  UnaryHistory bilinearTail ∧ UnaryHistory product ∧
                    UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                      Cont sourceA windowA leftFactor ∧ Cont sourceB windowB rightFactor ∧
                        Cont leftFactor rightFactor bilinearTail ∧
                          Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceAWindowLeft sourceBWindowRight factorTail classifierRealSeal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have leftFactorUnary : UnaryHistory leftFactor :=
    unary_cont_closed sourceAUnary windowAUnary sourceAWindowLeft
  have rightFactorUnary : UnaryHistory rightFactor :=
    unary_cont_closed sourceBUnary windowBUnary sourceBWindowRight
  have bilinearTailUnary : UnaryHistory bilinearTail :=
    unary_cont_closed leftFactorUnary rightFactorUnary factorTail
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRealSeal
  exact
    ⟨leftFactorUnary, rightFactorUnary, bilinearTailUnary, productUnary, classifierUnary,
      realSealUnary, sourceAWindowLeft, sourceBWindowRight, factorTail, classifierRoute,
      classifierRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
