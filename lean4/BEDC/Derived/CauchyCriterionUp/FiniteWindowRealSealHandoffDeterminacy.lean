import BEDC.Derived.CauchyCriterionUp.FiniteWindowRealSealHandoff
import BEDC.Derived.CauchyCriterionUp.LimitSealRouteStability

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_window_real_seal_handoff_determinacy
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      limitRead sealRead sealRead' comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont modulus regseq transport ->
        Cont transport window realSeal ->
          Cont realSeal route limitRead ->
            Cont route realSeal sealRead ->
              Cont route realSeal sealRead' ->
                Cont sealRead sealRead' comparison ->
                  PkgSig bundle limitRead pkg ->
                    PkgSig bundle comparison pkg ->
                      UnaryHistory limitRead ∧ hsame sealRead sealRead' ∧
                        UnaryHistory comparison ∧ Cont realSeal route limitRead ∧
                          Cont route realSeal sealRead ∧ Cont route realSeal sealRead' ∧
                            Cont sealRead sealRead' comparison ∧ PkgSig bundle limitRead pkg ∧
                              PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier modulusRegseqTransport transportWindowRealSeal realSealRouteLimit
    routeRealSealRead routeRealSealRead' sealComparison limitPkg comparisonPkg
  have handoff :
      UnaryHistory modulus ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
        UnaryHistory window ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
          UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory endpoint ∧
            UnaryHistory limitRead ∧ Cont modulus regseq transport ∧
              Cont transport window realSeal ∧ Cont realSeal route limitRead ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle limitRead pkg :=
    CauchyCriterionCarrier_finite_window_real_seal_handoff carrier modulusRegseqTransport
      transportWindowRealSeal realSealRouteLimit limitPkg
  have stability :
      hsame sealRead sealRead' ∧ UnaryHistory comparison ∧
        Cont route realSeal sealRead ∧ Cont route realSeal sealRead' ∧
          Cont sealRead sealRead' comparison ∧ PkgSig bundle comparison pkg :=
    CauchyCriterionCarrier_limit_seal_route_stability
      (window := window) (modulus := modulus) (tolerance := tolerance) (ledger := ledger)
      (regseq := regseq) (realSeal := realSeal) (transport := transport) (route := route)
      (provenance := provenance) (localCert := localCert) (endpoint := endpoint)
      (window' := window) (modulus' := modulus) (tolerance' := tolerance)
      (ledger' := ledger) (regseq' := regseq) (realSeal' := realSeal)
      (transport' := transport) (route' := route) (provenance' := provenance)
      (localCert' := localCert) (_endpoint' := endpoint) (sealRead := sealRead)
      (sealRead' := sealRead') (comparison := comparison) (bundle := bundle) (pkg := pkg)
      carrier (hsame_refl window) (hsame_refl modulus) (hsame_refl tolerance)
      (hsame_refl ledger) (hsame_refl regseq) (hsame_refl realSeal)
      (hsame_refl transport) (hsame_refl route) (hsame_refl provenance)
      (hsame_refl localCert) routeRealSealRead routeRealSealRead' sealComparison
      comparisonPkg
  exact
    ⟨handoff.right.right.right.right.right.right.right.right.right.left, stability.left,
      stability.right.left, realSealRouteLimit, routeRealSealRead, routeRealSealRead',
      sealComparison, limitPkg, comparisonPkg⟩

end BEDC.Derived.CauchyCriterionUp
