import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_finite_request_route_monotonicity
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n t' w' q' e' h' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame t t' ->
        hsame w w' ->
          hsame q q' ->
            hsame e e' ->
              Cont t' w' q' ->
                Cont q' e' h' ->
                  PkgSig bundle p pkg ->
                    UnaryHistory t' ∧ UnaryHistory w' ∧ UnaryHistory q' ∧
                      UnaryHistory e' ∧ UnaryHistory h' ∧ Cont t' w' q' ∧
                        Cont q' e' h' ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier sameT sameW sameQ sameE refinedWindow refinedSeal packageRow
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩ :=
    carrier
  have refinedTUnary : UnaryHistory t' :=
    unary_transport tUnary sameT
  have refinedWUnary : UnaryHistory w' :=
    unary_transport wUnary sameW
  have refinedQUnary : UnaryHistory q' :=
    unary_transport qUnary sameQ
  have refinedEUnary : UnaryHistory e' :=
    unary_transport eUnary sameE
  have refinedHUnary : UnaryHistory h' :=
    unary_cont_closed refinedQUnary refinedEUnary refinedSeal
  exact
    ⟨refinedTUnary, refinedWUnary, refinedQUnary, refinedEUnary, refinedHUnary,
      refinedWindow, refinedSeal, packageRow⟩

end BEDC.Derived.CauchyModulusRefinementUp
