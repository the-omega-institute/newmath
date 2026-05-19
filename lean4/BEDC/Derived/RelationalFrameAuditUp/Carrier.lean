import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RelationalFrameAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RelationalFrameAuditCarrier [AskSetup] [PackageSetup]
    (multiHist observerA observerB request symmetry causal rate refusal transport continuation
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory multiHist ∧ UnaryHistory observerA ∧ UnaryHistory observerB ∧
    UnaryHistory request ∧ UnaryHistory symmetry ∧ UnaryHistory causal ∧
      UnaryHistory rate ∧ UnaryHistory refusal ∧ UnaryHistory transport ∧
        UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont multiHist request observerA ∧ Cont request observerB causal ∧
            Cont causal symmetry rate ∧ Cont transport continuation provenance ∧
              PkgSig bundle provenance pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                  (fun row : BHist => hsame row provenance)
                  (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                  hsame

theorem RelationalFrameAuditCarrier_observer_symmetry_factorization [AskSetup]
    [PackageSetup]
    {multiHist observerA observerB request symmetry causal rate refusal transport continuation
      provenance name comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RelationalFrameAuditCarrier multiHist observerA observerB request symmetry causal rate
        refusal transport continuation provenance name bundle pkg ->
      Cont observerA observerB causal ->
        Cont causal rate comparison ->
          Cont comparison symmetry continuation ->
            PkgSig bundle comparison pkg ->
              UnaryHistory observerA ∧ UnaryHistory observerB ∧ UnaryHistory causal ∧
                UnaryHistory rate ∧ UnaryHistory comparison ∧
                  Cont observerA observerB causal ∧ Cont causal rate comparison ∧
                    Cont comparison symmetry continuation ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle comparison pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier observerRoute rateRoute symmetryRoute comparisonPkg
  obtain ⟨_multiHistUnary, observerAUnary, observerBUnary, _requestUnary, symmetryUnary,
    causalUnary, rateUnary, _refusalUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameUnary, _multiHistRoute, _requestRoute, _carrierRateRoute,
    _provenanceRoute, provenancePkg, _semanticCert⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed causalUnary rateUnary rateRoute
  exact
    ⟨observerAUnary,
      observerBUnary,
      causalUnary,
      rateUnary,
      comparisonUnary,
      observerRoute,
      rateRoute,
      symmetryRoute,
      provenancePkg,
      comparisonPkg⟩

end BEDC.Derived.RelationalFrameAuditUp
