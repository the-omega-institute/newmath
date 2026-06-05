import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalScopedFiniteModulusExport [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead barRead compactRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg →
      Cont C F prefixRead →
        Cont prefixRead B barRead →
          Cont barRead W compactRead →
            Cont compactRead M modulusRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  UnaryHistory prefixRead ∧ UnaryHistory barRead ∧
                    UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                      Cont C F prefixRead ∧ Cont prefixRead B barRead ∧
                        Cont barRead W compactRead ∧ Cont compactRead M modulusRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier prefixRoute barRoute compactRoute modulusRoute provenancePkg namePkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, _dUnary, wUnary, mUnary, _hUnary, _kUnary,
    _pUnary, _nUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary fUnary prefixRoute
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary bUnary barRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed barUnary wUnary compactRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed compactUnary mUnary modulusRoute
  exact
    ⟨prefixUnary, barUnary, compactUnary, modulusUnary, prefixRoute, barRoute,
      compactRoute, modulusRoute, provenancePkg, namePkg⟩

end BEDC.Derived.FanfunctionalUp
