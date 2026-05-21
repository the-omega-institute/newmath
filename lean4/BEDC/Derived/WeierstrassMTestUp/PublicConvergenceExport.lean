import BEDC.Derived.WeierstrassMTestUp

namespace BEDC.Derived.WeierstrassMTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeierstrassMTestCarrier_public_convergence_export [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name handoff
      sealRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont tail regseq handoff ->
        Cont regseq realSeal sealRead ->
          Cont sealRead route exportRead ->
            PkgSig bundle exportRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    WeierstrassMTestCarrier family majorant domination tail regseq realSeal
                      transport route provenance name bundle pkg ∧ hsame row provenance)
                  (fun row : BHist =>
                    WeierstrassMTestCarrier family majorant domination tail regseq realSeal
                      transport route provenance name bundle pkg ∧ hsame row provenance)
                  (fun row : BHist =>
                    WeierstrassMTestCarrier family majorant domination tail regseq realSeal
                      transport route provenance name bundle pkg ∧ hsame row provenance)
                  hsame ∧
                UnaryHistory handoff ∧ UnaryHistory sealRead ∧ UnaryHistory exportRead ∧
                  Cont tail regseq handoff ∧ Cont regseq realSeal sealRead ∧
                    Cont sealRead route exportRead ∧ hsame transport sealRead ∧
                      PkgSig bundle route pkg ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier tailRegseqHandoff regseqRealSealRead sealRouteExport exportPkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
            provenance name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
            provenance name bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
            provenance name bundle pkg ∧ hsame row provenance)
        hsame :=
    WeierstrassMTestCarrier_namecert_obligations carrier
  have handoffFacts :
      UnaryHistory handoff /\ UnaryHistory sealRead /\ Cont tail regseq handoff /\
        Cont regseq realSeal sealRead /\ hsame transport sealRead /\
          PkgSig bundle route pkg /\ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_uniform_cauchy_handoff carrier tailRegseqHandoff
      regseqRealSealRead
  obtain ⟨handoffUnary, sealReadUnary, tailRegseqHandoffRow, regseqRealSealReadRow,
    sameSeal, routePkg, namePkg⟩ := handoffFacts
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, _tailUnary, _regseqUnary,
    _realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, _dominationTailRegseq, _regseqRealSealTransport,
    _transportRouteProvenance, _routePkg, _namePkg⟩ := carrier
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary routeUnary sealRouteExport
  exact
    ⟨cert, handoffUnary, sealReadUnary, exportUnary, tailRegseqHandoffRow,
      regseqRealSealReadRow, sealRouteExport, sameSeal, routePkg, namePkg, exportPkg⟩

end BEDC.Derived.WeierstrassMTestUp
