import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_source_scoped_readback [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          hsame eta eta' →
            UnaryHistory routes →
              UnaryHistory name →
                Cont routes name sourceRead →
                  PkgSig bundle sourceRead pkg →
                    hsame analytic analytic' ∧ hsame transports transports' ∧
                      UnaryHistory sourceRead ∧ hsame sourceRead (append routes name) ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute etaSame routesUnary nameUnary routesNameSource
    sourceReadPkg
  have source :=
    ZetaContinuationWitnessPacket_source_boundary
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (bundle := bundle) (pkg := pkg)
      packet basicRoute functionalRoute etaSame
  obtain ⟨analyticSame, transportsSame, namePkg, provenancePkg⟩ := source
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed routesUnary nameUnary routesNameSource
  exact
    ⟨analyticSame, transportsSame, sourceReadUnary, routesNameSource, namePkg,
      provenancePkg, sourceReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
