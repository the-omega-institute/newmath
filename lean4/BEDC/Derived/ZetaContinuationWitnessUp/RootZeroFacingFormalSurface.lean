import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_root_zero_facing_formal_surface [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' zeroLedger' gamma' zeroRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont transports' routes provenance' →
            Cont pole zeroLedger' gamma' →
              PkgSig bundle provenance' pkg →
                hsame eta eta' →
                  hsame zeroLedger zeroLedger' →
                    UnaryHistory routes →
                      UnaryHistory name →
                        Cont routes name zeroRead →
                          PkgSig bundle zeroRead pkg →
                            hsame analytic analytic' ∧ hsame transports transports' ∧
                              hsame provenance provenance' ∧ hsame gamma gamma' ∧
                                UnaryHistory zeroRead ∧ hsame zeroRead (append routes name) ∧
                                  Cont basic eta' analytic' ∧
                                    Cont analytic' functional transports' ∧
                                      Cont transports' routes provenance' ∧
                                        Cont pole zeroLedger' gamma' ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig bundle provenance' pkg ∧
                                              PkgSig bundle zeroRead pkg ∧
                                                (Cont zeroRead (BHist.e0 hostTail) routes →
                                                  False) ∧
                                                  (Cont zeroRead (BHist.e1 hostTail) routes →
                                                    False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute provenanceRoute gammaRoute provenancePkg etaSame
    zeroLedgerSame routesUnary nameUnary routesNameZero zeroReadPkg
  have readiness :=
    ZetaContinuationWitnessPacket_root_readiness_lock
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (zeroLedger' := zeroLedger') (gamma' := gamma') (rootRead := zeroRead)
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      gammaRoute provenancePkg etaSame zeroLedgerSame routesUnary nameUnary routesNameZero
  obtain ⟨analyticSame, transportsSame, provenanceSame, gammaSame, zeroReadUnary,
    zeroReadSame, namePkg, provenancePkg'⟩ := readiness
  exact
    ⟨analyticSame, transportsSame, provenanceSame, gammaSame, zeroReadUnary, zeroReadSame,
      basicRoute, functionalRoute, provenanceRoute, gammaRoute, namePkg, provenancePkg',
      zeroReadPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left routesNameZero hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right routesNameZero hostReturn)⟩

end BEDC.Derived.ZetaContinuationWitnessUp
