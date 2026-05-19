import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_source_lock_coverage [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          hsame eta eta' ->
            UnaryHistory routes ->
              UnaryHistory name ->
                Cont routes name exportRow ->
                  hsame analytic analytic' ∧ hsame transports transports' ∧
                    UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute etaSame routesUnary nameUnary routesNameExport
  obtain ⟨basicAnalytic, analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticTransport functionalRoute
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  exact
    ⟨analyticSame, transportsSame, exportUnary, routesNameExport, namePkg,
      provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
