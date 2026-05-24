import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeierstrassMTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WeierstrassMTestCarrier [AskSetup] [PackageSetup]
    (family majorant domination tail regseq realSeal transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory majorant ∧ UnaryHistory domination ∧
    UnaryHistory tail ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont family majorant domination ∧ Cont domination tail regseq ∧
          Cont regseq realSeal transport ∧ Cont transport route provenance ∧
            PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem WeierstrassMTestCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
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
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem WeierstrassMTestCarrier_majorant_tail_transport [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name tail'
      regseq' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      hsame tail tail' ->
        Cont domination tail' regseq' ->
          WeierstrassMTestCarrier family majorant domination tail' regseq' realSeal transport
              route provenance name bundle pkg ∧ hsame regseq regseq' := by
  intro carrier sameTail newTailRoute
  obtain ⟨familyUnary, majorantUnary, dominationUnary, tailUnary, regseqUnary, realSealUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, familyMajorantDomination,
    dominationTailRegseq, regseqRealSealTransport, transportRouteProvenance, routePkg,
    namePkg⟩ := carrier
  have tailUnary' : UnaryHistory tail' :=
    unary_transport tailUnary sameTail
  have regseqUnary' : UnaryHistory regseq' :=
    unary_cont_closed dominationUnary tailUnary' newTailRoute
  have sameRegseq : hsame regseq regseq' :=
    cont_respects_hsame (hsame_refl domination) sameTail dominationTailRegseq newTailRoute
  have regseqRealSealTransport' : Cont regseq' realSeal transport := by
    cases sameRegseq
    exact regseqRealSealTransport
  exact
    ⟨⟨familyUnary, majorantUnary, dominationUnary, tailUnary', regseqUnary',
        realSealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
        familyMajorantDomination, newTailRoute, regseqRealSealTransport',
        transportRouteProvenance, routePkg, namePkg⟩,
      sameRegseq⟩

theorem WeierstrassMTestCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont tail regseq handoff ->
        UnaryHistory handoff ∧ Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
          PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  intro carrier tailRegseqHandoff
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, tailUnary, regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, _dominationTailRegseq, regseqRealSealTransport,
    _transportRouteProvenance, routePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed tailUnary regseqUnary tailRegseqHandoff
  exact
    ⟨handoffUnary, tailRegseqHandoff, regseqRealSealTransport, routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont regseq realSeal sealRead ->
        UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
          Cont regseq realSeal transport ∧ Cont regseq realSeal sealRead ∧
            hsame transport sealRead ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  intro carrier regseqRealSealRead
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, _tailUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, _dominationTailRegseq, regseqRealSealTransport,
    _transportRouteProvenance, routePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealRead
  have sameSealRead : hsame transport sealRead :=
    cont_respects_hsame (hsame_refl regseq) (hsame_refl realSeal) regseqRealSealTransport
      regseqRealSealRead
  exact
    ⟨regseqUnary, realSealUnary, sealReadUnary, regseqRealSealTransport, regseqRealSealRead,
      sameSealRead, routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_tail_majorant_ledger [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont domination tail tailRead ->
        UnaryHistory family ∧ UnaryHistory majorant ∧ UnaryHistory domination ∧
          UnaryHistory tail ∧ UnaryHistory tailRead ∧ Cont family majorant domination ∧
            Cont domination tail regseq ∧ Cont domination tail tailRead ∧
              hsame regseq tailRead ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  intro carrier dominationTailRead
  obtain ⟨familyUnary, majorantUnary, dominationUnary, tailUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    familyMajorantDomination, dominationTailRegseq, _regseqRealSealTransport,
    _transportRouteProvenance, routePkg, namePkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed dominationUnary tailUnary dominationTailRead
  have sameTailRead : hsame regseq tailRead :=
    cont_respects_hsame (hsame_refl domination) (hsame_refl tail) dominationTailRegseq
      dominationTailRead
  exact
    ⟨familyUnary, majorantUnary, dominationUnary, tailUnary, tailReadUnary,
      familyMajorantDomination, dominationTailRegseq, dominationTailRead, sameTailRead,
      routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name handoff
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont tail regseq handoff ->
        Cont regseq realSeal sealRead ->
          UnaryHistory handoff ∧ UnaryHistory sealRead ∧ Cont domination tail regseq ∧
            Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
              Cont regseq realSeal sealRead ∧ hsame transport sealRead ∧
                PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  intro carrier tailRegseqHandoff regseqRealSealRead
  have handoffFacts :
      UnaryHistory handoff ∧ Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
        PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_regseqrat_handoff carrier tailRegseqHandoff
  have sealFacts :
      UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
        Cont regseq realSeal transport ∧ Cont regseq realSeal sealRead ∧
          hsame transport sealRead ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_real_seal_factorization carrier regseqRealSealRead
  obtain ⟨handoffUnary, tailRegseqRoute, _handoffSealRoute, _handoffRoutePkg,
    _handoffNamePkg⟩ := handoffFacts
  obtain ⟨_regseqUnary, _realSealUnary, sealReadUnary, regseqRealSealTransport,
    regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩ := sealFacts
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, _tailUnary, _regseqUnaryCarrier,
    _realSealUnaryCarrier, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, dominationTailRegseq, _carrierSealRoute,
    _transportRouteProvenance, _carrierRoutePkg, _carrierNamePkg⟩ := carrier
  exact
    ⟨handoffUnary, sealReadUnary, dominationTailRegseq, tailRegseqRoute,
      regseqRealSealTransport, regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_uniform_cauchy_handoff [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name handoff
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont tail regseq handoff ->
        Cont regseq realSeal sealRead ->
          UnaryHistory handoff /\ UnaryHistory sealRead /\ Cont tail regseq handoff /\
            Cont regseq realSeal sealRead /\ hsame transport sealRead /\
              PkgSig bundle route pkg /\ PkgSig bundle name pkg := by
  intro carrier tailRegseqHandoff regseqRealSealRead
  have closure :
      UnaryHistory handoff ∧ UnaryHistory sealRead ∧ Cont domination tail regseq ∧
        Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
          Cont regseq realSeal sealRead ∧ hsame transport sealRead ∧
            PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_obligation_closure_package carrier tailRegseqHandoff
      regseqRealSealRead
  obtain ⟨handoffUnary, sealReadUnary, _dominationTailRegseq, tailRegseqRoute,
    _regseqRealSealTransport, regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩ :=
    closure
  exact
    ⟨handoffUnary, sealReadUnary, tailRegseqRoute, regseqRealSealReadRow, sameSealRead,
      routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_uniform_tail_budget_scope [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name handoff
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont tail regseq handoff ->
        Cont regseq realSeal sealRead ->
          UnaryHistory handoff ∧ UnaryHistory sealRead ∧ Cont domination tail regseq ∧
            Cont tail regseq handoff ∧ Cont regseq realSeal sealRead ∧
              hsame transport sealRead ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier tailRegseqHandoff regseqRealSealRead
  have closure :
      UnaryHistory handoff ∧ UnaryHistory sealRead ∧ Cont domination tail regseq ∧
        Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
          Cont regseq realSeal sealRead ∧ hsame transport sealRead ∧
            PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_obligation_closure_package carrier tailRegseqHandoff
      regseqRealSealRead
  obtain ⟨handoffUnary, sealReadUnary, dominationTailRegseq, tailRegseqRoute,
    _regseqRealSealTransport, regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩ :=
    closure
  exact
    ⟨handoffUnary, sealReadUnary, dominationTailRegseq, tailRegseqRoute,
      regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg ->
      Cont regseq realSeal sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
            Cont regseq realSeal sealRead ∧ PkgSig bundle name pkg ∧
              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier regseqRealSealRead sealReadPkg
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, _tailUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, _dominationTailRegseq, _regseqRealSealTransport,
    _transportRouteProvenance, _routePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealRead
  exact
    ⟨regseqUnary, realSealUnary, sealReadUnary, regseqRealSealRead, namePkg, sealReadPkg⟩

def WeierstrassMTestObligationSurface [AskSetup] [PackageSetup]
    (family majorant domination tail regseq realSeal transport route provenance name
      obligationRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
      provenance name bundle pkg ∧
    Cont domination tail regseq ∧ Cont tail regseq obligationRead ∧
      PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem WeierstrassMTestObligationSurface_namecert_rows [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestObligationSurface family majorant domination tail regseq realSeal
        transport route provenance name obligationRead bundle pkg →
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
        UnaryHistory obligationRead ∧ Cont tail regseq obligationRead ∧
          PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro surface
  obtain ⟨carrier, _dominationTailRegseq, tailRegseqObligation, routePkg, namePkg⟩ :=
    surface
  have carrierForCert := carrier
  obtain ⟨_familyUnary, _majorantUnary, _dominationUnary, tailUnary, regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _familyMajorantDomination, _carrierDominationTailRegseq, _regseqRealSealTransport,
    _transportRouteProvenance, _carrierRoutePkg, _carrierNamePkg⟩ := carrier
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed tailUnary regseqUnary tailRegseqObligation
  exact
    ⟨WeierstrassMTestCarrier_namecert_obligations carrierForCert, obligationUnary,
      tailRegseqObligation, routePkg, namePkg⟩

theorem WeierstrassMTestCarrier_scoped_dependency_package [AskSetup] [PackageSetup]
    {family majorant domination tail regseq realSeal transport route provenance name handoff
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassMTestCarrier family majorant domination tail regseq realSeal transport route
        provenance name bundle pkg →
      Cont tail regseq handoff →
        Cont regseq realSeal sealRead →
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
            UnaryHistory handoff ∧ UnaryHistory sealRead ∧ hsame transport sealRead ∧
              PkgSig bundle route pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier tailRegseqHandoff regseqRealSealRead
  have cert :
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
        hsame :=
    WeierstrassMTestCarrier_namecert_obligations carrier
  have handoffFacts :
      UnaryHistory handoff ∧ Cont tail regseq handoff ∧ Cont regseq realSeal transport ∧
        PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_regseqrat_handoff carrier tailRegseqHandoff
  have sealFacts :
      UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
        Cont regseq realSeal transport ∧ Cont regseq realSeal sealRead ∧
          hsame transport sealRead ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg :=
    WeierstrassMTestCarrier_real_seal_factorization carrier regseqRealSealRead
  obtain ⟨handoffUnary, _tailRegseqRoute, _regseqRealSealTransport, _routePkgFromHandoff,
    _namePkgFromHandoff⟩ := handoffFacts
  obtain ⟨_regseqUnary, _realSealUnary, sealReadUnary, _regseqRealSealTransport',
    _regseqRealSealReadRow, sameSealRead, routePkg, namePkg⟩ := sealFacts
  exact ⟨cert, handoffUnary, sealReadUnary, sameSealRead, routePkg, namePkg⟩

end BEDC.Derived.WeierstrassMTestUp
