import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverMeshRefinementInduction [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N baseRead stepRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory R ->
        UnaryHistory V ->
          UnaryHistory A ->
            Cont M R baseRead ->
              Cont baseRead V stepRead ->
                Cont stepRead A sealRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle sealRead pkg ->
                      hsame M M ∧ UnaryHistory baseRead ∧ UnaryHistory stepRead ∧
                        UnaryHistory sealRead ∧ Cont M R baseRead ∧
                          Cont baseRead V stepRead ∧ Cont stepRead A sealRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro mUnary rUnary vUnary aUnary baseRoute stepRoute sealRoute provenancePkg sealPkg
  have baseUnary : UnaryHistory baseRead :=
    unary_cont_closed mUnary rUnary baseRoute
  have stepUnary : UnaryHistory stepRead :=
    unary_cont_closed baseUnary vUnary stepRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed stepUnary aUnary sealRoute
  exact
    ⟨hsame_refl M, baseUnary, stepUnary, sealUnary, baseRoute, stepRoute, sealRoute,
      provenancePkg, sealPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
