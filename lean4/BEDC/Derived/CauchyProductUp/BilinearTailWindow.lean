import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_bilinear_tail_window [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name leftFactor rightFactor bilinearTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont sourceA windowA leftFactor ->
        Cont sourceB windowB rightFactor ->
          Cont leftFactor rightFactor bilinearTail ->
            UnaryHistory leftFactor ∧ UnaryHistory rightFactor ∧
              UnaryHistory bilinearTail ∧ UnaryHistory product ∧
                Cont sourceA windowA leftFactor ∧ Cont sourceB windowB rightFactor ∧
                  Cont leftFactor rightFactor bilinearTail ∧
                    Cont observationA observationB product ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceLeft sourceRight factorsTail
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have leftUnary : UnaryHistory leftFactor :=
    unary_cont_closed sourceAUnary windowAUnary sourceLeft
  have rightUnary : UnaryHistory rightFactor :=
    unary_cont_closed sourceBUnary windowBUnary sourceRight
  have tailUnary : UnaryHistory bilinearTail :=
    unary_cont_closed leftUnary rightUnary factorsTail
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  exact
    ⟨leftUnary, rightUnary, tailUnary, productUnary, sourceLeft, sourceRight, factorsTail,
      productRoute, namePkg⟩

end BEDC.Derived.CauchyProductUp
