import BEDC.Derived.MetricUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem MetricspaceL10SiblingLatticeRoute_finite_packet [AskSetup] [PackageSetup]
    {located sone real stream regseq dyadic route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory located ->
      UnaryHistory sone ->
        UnaryHistory stream ->
          UnaryHistory dyadic ->
            UnaryHistory provenance ->
              Cont located sone real ->
                Cont real stream regseq ->
                  Cont regseq dyadic route ->
                    Cont route provenance endpoint ->
                      PkgSig bundle endpoint pkg ->
                        UnaryHistory real ∧ UnaryHistory regseq ∧ UnaryHistory route ∧
                          UnaryHistory endpoint ∧ Cont located sone real ∧
                            Cont real stream regseq ∧ Cont regseq dyadic route ∧
                              Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro locatedUnary soneUnary streamUnary dyadicUnary provenanceUnary locatedSoneReal
    realStreamRegseq regseqDyadicRoute routeProvenanceEndpoint endpointPkg
  have realUnary : UnaryHistory real :=
    unary_cont_closed locatedUnary soneUnary locatedSoneReal
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed realUnary streamUnary realStreamRegseq
  have routeUnary : UnaryHistory route :=
    unary_cont_closed regseqUnary dyadicUnary regseqDyadicRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceEndpoint
  exact
    ⟨realUnary, regseqUnary, routeUnary, endpointUnary, locatedSoneReal, realStreamRegseq,
      regseqDyadicRoute, routeProvenanceEndpoint, endpointPkg⟩

theorem MetricSpaceL10SiblingLatticeRoute [AskSetup] [PackageSetup]
    {located sone real stream regseq dyadic locatedRoute soneRoute realRoute l10 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory located → UnaryHistory sone → UnaryHistory real → UnaryHistory stream →
      UnaryHistory regseq → UnaryHistory dyadic → Cont located sone locatedRoute →
        Cont stream regseq soneRoute → Cont dyadic real realRoute →
          Cont locatedRoute soneRoute l10 → PkgSig bundle l10 pkg →
            UnaryHistory l10 ∧ UnaryHistory realRoute ∧
              Cont locatedRoute soneRoute l10 ∧ Cont dyadic real realRoute ∧
                PkgSig bundle l10 pkg ∧ MetricDistanceWitness locatedRoute soneRoute l10 ∧
                  SemanticNameCert (MetricDistanceWitness locatedRoute soneRoute)
                    (MetricDistanceWitness locatedRoute soneRoute)
                    (MetricDistanceWitness locatedRoute soneRoute) hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro locatedUnary soneUnary realUnary streamUnary regseqUnary dyadicUnary
    locatedSone streamRegseq dyadicReal locatedRouteSoneRoute l10Pkg
  have locatedRouteUnary : UnaryHistory locatedRoute :=
    unary_cont_closed locatedUnary soneUnary locatedSone
  have soneRouteUnary : UnaryHistory soneRoute :=
    unary_cont_closed streamUnary regseqUnary streamRegseq
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed dyadicUnary realUnary dyadicReal
  have l10Unary : UnaryHistory l10 :=
    unary_cont_closed locatedRouteUnary soneRouteUnary locatedRouteSoneRoute
  have distanceWitness : MetricDistanceWitness locatedRoute soneRoute l10 :=
    ⟨locatedRouteUnary, soneRouteUnary, l10Unary, locatedRouteSoneRoute⟩
  exact
    ⟨l10Unary, realRouteUnary, locatedRouteSoneRoute, dyadicReal, l10Pkg,
      distanceWitness,
      MetricDistanceWitness_semanticNameCert locatedRouteUnary soneRouteUnary⟩

end BEDC.Derived.MetricUp
