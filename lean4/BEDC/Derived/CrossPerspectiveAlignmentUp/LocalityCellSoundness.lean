import BEDC.Derived.CrossPerspectiveAlignmentUp.NameCertObligations

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossPerspectiveAlignmentCarrier_locality_cell_soundness [AskSetup] [PackageSetup]
    {source target locality commitment multiHist transports routes provenance nameCert
      localityRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports routes
        provenance nameCert bundle pkg ->
      Cont locality commitment localityRead ->
        Cont source target publicRead ->
          PkgSig bundle localityRead pkg ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory locality ∧
                UnaryHistory commitment ∧ UnaryHistory multiHist ∧ UnaryHistory localityRead ∧
                  UnaryHistory publicRead ∧ Cont locality commitment localityRead ∧
                    Cont source target publicRead ∧ hsame nameCert source ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle localityRead pkg ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier localityCommitmentRead sourceTargetPublic localityPkg publicPkg
  obtain ⟨sourceUnary, targetUnary, localityUnary, commitmentUnary, multiHistUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, nameCertSameSource,
    provenancePkg⟩ := carrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary commitmentUnary localityCommitmentRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary targetUnary sourceTargetPublic
  exact
    ⟨sourceUnary, targetUnary, localityUnary, commitmentUnary, multiHistUnary,
      localityReadUnary, publicReadUnary, localityCommitmentRead, sourceTargetPublic,
      nameCertSameSource, provenancePkg, localityPkg, publicPkg⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
