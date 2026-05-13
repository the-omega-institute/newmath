import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CollisionKernelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CollisionKernelCarrier [AskSetup] [PackageSetup]
    (window fold ledger matrix moment shadow transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧ UnaryHistory matrix ∧
    UnaryHistory moment ∧ UnaryHistory shadow ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont window fold ledger ∧
        Cont ledger matrix shadow ∧ Cont moment matrix shadow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg

theorem CollisionKernelCarrier_zero_window_packet [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧ UnaryHistory matrix ∧
        UnaryHistory moment ∧ UnaryHistory shadow ∧ Cont window fold ledger ∧
          Cont ledger matrix shadow ∧ Cont moment matrix shadow ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute,
    momentRoute, provenancePkg, _nameCertPkg⟩ := carrier
  exact
    ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary, windowRoute,
      ledgerRoute, momentRoute, provenancePkg⟩

theorem CollisionKernelCarrier_hankel_shadow_boundary [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont moment matrix shadowRead ->
        hsame shadowRead shadow ->
          UnaryHistory moment ∧ UnaryHistory matrix ∧ UnaryHistory shadow ∧
            UnaryHistory shadowRead ∧ Cont ledger matrix shadow ∧ Cont moment matrix shadow ∧
              Cont moment matrix shadowRead ∧ hsame shadowRead shadow ∧
                PkgSig bundle provenance pkg := by
  intro carrier shadowReadRoute shadowReadSame
  obtain ⟨_windowUnary, _foldUnary, _ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowRoute, ledgerRoute,
    momentRoute, provenancePkg, _nameCertPkg⟩ := carrier
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed momentUnary matrixUnary shadowReadRoute
  exact
    ⟨momentUnary, matrixUnary, shadowUnary, shadowReadUnary, ledgerRoute, momentRoute,
      shadowReadRoute, shadowReadSame, provenancePkg⟩

theorem CollisionKernelCarrier_fiber_ledger_exactness [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert
      matrixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont ledger matrix matrixRead ->
        UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧ UnaryHistory matrix ∧
          UnaryHistory matrixRead ∧ Cont window fold ledger ∧ Cont ledger matrix shadow ∧
            Cont ledger matrix matrixRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier matrixRoute
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, _momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute,
    _momentRoute, provenancePkg, _nameCertPkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixRoute
  exact
    ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, matrixReadUnary, windowRoute,
      ledgerRoute, matrixRoute, provenancePkg⟩

theorem CollisionKernelCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert matrixRead
      shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont ledger matrix matrixRead ->
        Cont moment matrix shadowRead ->
          hsame shadowRead shadow ->
            UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧
              UnaryHistory matrix ∧ UnaryHistory moment ∧ UnaryHistory shadow ∧
                UnaryHistory matrixRead ∧ UnaryHistory shadowRead ∧ Cont window fold ledger ∧
                  Cont ledger matrix shadow ∧ Cont ledger matrix matrixRead ∧
                    Cont moment matrix shadow ∧ Cont moment matrix shadowRead ∧
                      hsame shadowRead shadow ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier matrixRoute shadowReadRoute shadowReadSame
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute, ledgerRoute,
    momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixRoute
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed momentUnary matrixUnary shadowReadRoute
  exact
    ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary, matrixReadUnary,
      shadowReadUnary, windowRoute, ledgerRoute, matrixRoute, momentRoute, shadowReadRoute,
      shadowReadSame, provenancePkg, nameCertPkg⟩

theorem CollisionKernelCarrier_moment_readback_exhaustion [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert momentRead
      shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont moment matrix momentRead ->
        Cont moment matrix shadowRead ->
          hsame momentRead shadow ->
            UnaryHistory moment ∧ UnaryHistory matrix ∧ UnaryHistory shadow ∧
              UnaryHistory momentRead ∧ UnaryHistory shadowRead ∧ Cont moment matrix shadow ∧
                Cont moment matrix momentRead ∧ Cont moment matrix shadowRead ∧
                  hsame momentRead shadow ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier momentReadRoute shadowReadRoute momentReadSame
  obtain ⟨_windowUnary, _foldUnary, _ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowRoute,
    _ledgerRoute, momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  have momentReadUnary : UnaryHistory momentRead :=
    unary_cont_closed momentUnary matrixUnary momentReadRoute
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed momentUnary matrixUnary shadowReadRoute
  exact
    ⟨momentUnary, matrixUnary, shadowUnary, momentReadUnary, shadowReadUnary, momentRoute,
      momentReadRoute, shadowReadRoute, momentReadSame, provenancePkg, nameCertPkg⟩

end BEDC.Derived.CollisionKernelUp
