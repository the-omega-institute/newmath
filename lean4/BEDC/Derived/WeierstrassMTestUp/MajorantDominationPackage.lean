import BEDC.Derived.WeierstrassMTestUp

namespace BEDC.Derived.WeierstrassMTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeierstrassMTestCarrier_majorant_domination_package [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      dominationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg →
      Cont family majorant dominationRead →
        SemanticNameCert
            (fun row : BHist =>
              WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
                route provenance name bundle pkg ∧ hsame row provenance)
            (fun row : BHist =>
              WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
                route provenance name bundle pkg ∧ hsame row provenance)
            (fun row : BHist =>
              WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport
                route provenance name bundle pkg ∧ hsame row provenance)
            hsame ∧
          UnaryHistory dominationRead ∧ hsame domination dominationRead ∧
            Cont family majorant dominationRead ∧ PkgSig bundle route pkg ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier familyMajorantRead
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
  obtain ⟨familyUnary, majorantUnary, _dominationUnary, _tailUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    familyMajorantDomination, _dominationTailRegseq, _regseqRealSealTransport,
    _transportRouteProvenance, routePkg, namePkg⟩ := carrier
  have dominationReadUnary : UnaryHistory dominationRead :=
    unary_cont_closed familyUnary majorantUnary familyMajorantRead
  have sameDomination : hsame domination dominationRead :=
    cont_respects_hsame (hsame_refl family) (hsame_refl majorant) familyMajorantDomination
      familyMajorantRead
  exact
    ⟨cert, dominationReadUnary, sameDomination, familyMajorantRead, routePkg, namePkg⟩

end BEDC.Derived.WeierstrassMTestUp
