import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v h refusalRead ->
        Cont h c transportRead ->
          PkgSig bundle refusalRead pkg ->
            PkgSig bundle transportRead pkg ->
              UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory refusalRead ∧
                  UnaryHistory transportRead ∧ Cont e a v ∧ Cont e t h ∧
                    Cont v h refusalRead ∧ Cont h c transportRead ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle refusalRead pkg ∧
                        PkgSig bundle transportRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier refusalRoute transportRoute refusalPkg transportPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, _nUnary, routeV,
    routeH, _routeN, pPkg, _nPkg, sameHN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary refusalRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed hUnary cUnary transportRoute
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, refusalUnary, transportUnary,
      routeV, routeH, refusalRoute, transportRoute, pPkg, refusalPkg, transportPkg,
      sameHN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
