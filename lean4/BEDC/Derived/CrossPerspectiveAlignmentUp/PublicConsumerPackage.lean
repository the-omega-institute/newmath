import BEDC.Derived.CrossPerspectiveAlignmentUp.NameCertObligations

namespace BEDC.Derived.CrossPerspectiveAlignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CrossPerspectiveAlignmentCarrier_public_consumer_package [AskSetup] [PackageSetup]
    {source target locality commitment multiHist transports routes provenance nameCert localityRead
      identityRead coherenceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CrossPerspectiveAlignmentCarrier source target locality commitment multiHist transports routes
        provenance nameCert bundle pkg ->
      Cont locality commitment localityRead ->
        Cont target commitment identityRead ->
          Cont multiHist transports coherenceRead ->
            Cont source target publicRead ->
              PkgSig bundle localityRead pkg ->
                PkgSig bundle identityRead pkg ->
                  PkgSig bundle coherenceRead pkg ->
                    PkgSig bundle publicRead pkg ->
                      UnaryHistory localityRead ∧ UnaryHistory identityRead ∧
                        UnaryHistory coherenceRead ∧ UnaryHistory publicRead ∧
                          Cont locality commitment localityRead ∧
                            Cont target commitment identityRead ∧
                              Cont multiHist transports coherenceRead ∧
                                Cont source target publicRead ∧ hsame nameCert source ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localityRead pkg ∧
                                      PkgSig bundle identityRead pkg ∧
                                        PkgSig bundle coherenceRead pkg ∧
                                          PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier localityCommitmentRead targetCommitmentRead multiHistTransportsRead
    sourceTargetPublic localityPkg identityPkg coherencePkg publicPkg
  obtain ⟨sourceUnary, targetUnary, localityUnary, commitmentUnary, multiHistUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, nameCertSameSource,
    provenancePkg⟩ := carrier
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed localityUnary commitmentUnary localityCommitmentRead
  have identityReadUnary : UnaryHistory identityRead :=
    unary_cont_closed targetUnary commitmentUnary targetCommitmentRead
  have coherenceReadUnary : UnaryHistory coherenceRead :=
    unary_cont_closed multiHistUnary transportsUnary multiHistTransportsRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary targetUnary sourceTargetPublic
  exact
    ⟨localityReadUnary, identityReadUnary, coherenceReadUnary, publicReadUnary,
      localityCommitmentRead, targetCommitmentRead, multiHistTransportsRead,
      sourceTargetPublic, nameCertSameSource, provenancePkg, localityPkg, identityPkg,
      coherencePkg, publicPkg⟩

end BEDC.Derived.CrossPerspectiveAlignmentUp
