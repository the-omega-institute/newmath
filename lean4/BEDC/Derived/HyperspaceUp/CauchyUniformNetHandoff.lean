import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceCauchyUniformNetHandoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M netLeft netRight directedRead publicRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 N0 netLeft →
        Cont K1 N1 netRight →
          Cont netLeft netRight directedRead →
            Cont directedRead R publicRead →
              Cont C publicRead replayRead →
                PkgSig bundle M pkg →
                  UnaryHistory netLeft ∧ UnaryHistory netRight ∧
                    UnaryHistory directedRead ∧ UnaryHistory publicRead ∧
                      UnaryHistory replayRead ∧ hsame directedRead (append netLeft netRight) ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle M pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier netLeftRoute netRightRoute directedRoute publicRoute replayRoute namePkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    rUnary, _hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have netLeftUnary : UnaryHistory netLeft :=
    unary_cont_closed k0Unary n0Unary netLeftRoute
  have netRightUnary : UnaryHistory netRight :=
    unary_cont_closed k1Unary n1Unary netRightRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed netLeftUnary netRightUnary directedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed directedUnary rUnary publicRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed cUnary publicUnary replayRoute
  have directedExact : hsame directedRead (append netLeft netRight) := directedRoute
  exact
    ⟨netLeftUnary, netRightUnary, directedUnary, publicUnary, replayUnary, directedExact,
      provenancePkg, namePkg⟩

end BEDC.Derived.HyperspaceUp
