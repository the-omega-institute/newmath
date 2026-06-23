import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CollisionKernelUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CollisionKernelCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert matrixRead
      shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont ledger matrix matrixRead ->
        Cont moment matrix shadowRead ->
          hsame shadowRead shadow ->
            SemanticNameCert
                (fun row : BHist => hsame row shadowRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row window ∨ hsame row fold ∨ hsame row ledger ∨ hsame row matrix ∨
                    hsame row moment ∨ hsame row shadow ∨ hsame row matrixRead ∨
                      hsame row shadowRead ∨ hsame row nameCert)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont window fold ledger ∧
                    Cont ledger matrix matrixRead ∧ Cont moment matrix shadowRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
                hsame ∧ UnaryHistory matrixRead ∧ UnaryHistory shadowRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier matrixRoute shadowReadRoute _shadowReadSame
  obtain ⟨_windowUnary, _foldUnary, ledgerUnary, matrixUnary, momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute,
    _ledgerShadowRoute, _momentShadowRoute, provenancePkg, nameCertPkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixRoute
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed momentUnary matrixUnary shadowReadRoute
  have sourceShadowRead : hsame shadowRead shadowRead ∧ UnaryHistory shadowRead :=
    ⟨hsame_refl shadowRead, shadowReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row shadowRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row window ∨ hsame row fold ∨ hsame row ledger ∨ hsame row matrix ∨
            hsame row moment ∨ hsame row shadow ∨ hsame row matrixRead ∨
              hsame row shadowRead ∨ hsame row nameCert)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont window fold ledger ∧ Cont ledger matrix matrixRead ∧
            Cont moment matrix shadowRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameCert pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro shadowRead sourceShadowRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, matrixRoute, shadowReadRoute, provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, matrixReadUnary, shadowReadUnary⟩

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

theorem CollisionKernelMomentLedgerNoninterference [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert momentRead
      shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont moment matrix momentRead ->
        Cont moment matrix shadowRead ->
          hsame momentRead shadow ->
            UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory matrix ∧
              UnaryHistory provenance ∧ UnaryHistory nameCert ∧
                Cont moment matrix momentRead ∧ Cont moment matrix shadowRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier momentReadRoute shadowReadRoute _momentReadSame
  obtain ⟨windowUnary, foldUnary, _ledgerUnary, matrixUnary, _momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, provenanceUnary, nameCertUnary, _windowRoute, _ledgerRoute,
    _momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  exact
    ⟨windowUnary, foldUnary, matrixUnary, provenanceUnary, nameCertUnary, momentReadRoute,
      shadowReadRoute, provenancePkg, nameCertPkg⟩

theorem CollisionKernelCarrier_zero_window_determinacy [AskSetup] [PackageSetup]
    {window fold ledger matrix moment moment' shadow shadow' transport route provenance nameCert
      transport' route' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg →
      CollisionKernelCarrier window fold ledger matrix moment' shadow' transport' route'
          provenance' nameCert' bundle pkg →
        hsame shadow shadow' ∧ UnaryHistory window ∧ UnaryHistory fold ∧
          UnaryHistory ledger ∧ UnaryHistory matrix ∧ Cont window fold ledger ∧
            Cont ledger matrix shadow ∧ Cont ledger matrix shadow' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro leftCarrier rightCarrier
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, _momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowRoute,
    ledgerShadow, _momentShadow, _provenancePkg, _nameCertPkg⟩ := leftCarrier
  obtain ⟨_windowUnary', _foldUnary', _ledgerUnary', _matrixUnary', _momentUnary',
    _shadowUnary', _transportUnary', _routeUnary', _provenanceUnary', _nameCertUnary',
    _windowRoute', ledgerShadow', _momentShadow', _provenancePkg', _nameCertPkg'⟩ :=
    rightCarrier
  exact
    ⟨cont_deterministic ledgerShadow ledgerShadow', windowUnary, foldUnary, ledgerUnary,
      matrixUnary, windowRoute, ledgerShadow, ledgerShadow'⟩

theorem CollisionKernelCarrier_classifier_transport_scope [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert window' fold'
      ledger' matrix' moment' shadow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      hsame window' window ->
        hsame fold' fold ->
          hsame ledger' ledger ->
            hsame matrix' matrix ->
              hsame moment' moment ->
                hsame shadow' shadow ->
                  Cont window' fold' ledger' ->
                    Cont ledger' matrix' shadow' ->
                      Cont moment' matrix' shadow' ->
                        UnaryHistory window' ∧ UnaryHistory fold' ∧ UnaryHistory ledger' ∧
                          UnaryHistory matrix' ∧ UnaryHistory moment' ∧ UnaryHistory shadow' ∧
                            CollisionKernelCarrier window' fold' ledger' matrix' moment' shadow'
                              transport route provenance nameCert bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier sameWindow sameFold sameLedger sameMatrix sameMoment sameShadow windowRoute'
    ledgerRoute' momentRoute'
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, momentUnary, shadowUnary,
    transportUnary, routeUnary, provenanceUnary, nameCertUnary, _windowRoute, _ledgerRoute,
    _momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  have windowUnary' : UnaryHistory window' :=
    unary_transport_symm windowUnary sameWindow
  have foldUnary' : UnaryHistory fold' :=
    unary_transport_symm foldUnary sameFold
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport_symm ledgerUnary sameLedger
  have matrixUnary' : UnaryHistory matrix' :=
    unary_transport_symm matrixUnary sameMatrix
  have momentUnary' : UnaryHistory moment' :=
    unary_transport_symm momentUnary sameMoment
  have shadowUnary' : UnaryHistory shadow' :=
    unary_transport_symm shadowUnary sameShadow
  have transportedCarrier :
      CollisionKernelCarrier window' fold' ledger' matrix' moment' shadow' transport route
        provenance nameCert bundle pkg :=
    ⟨windowUnary', foldUnary', ledgerUnary', matrixUnary', momentUnary', shadowUnary',
      transportUnary, routeUnary, provenanceUnary, nameCertUnary, windowRoute', ledgerRoute',
      momentRoute', provenancePkg, nameCertPkg⟩
  exact
    ⟨windowUnary', foldUnary', ledgerUnary', matrixUnary', momentUnary', shadowUnary',
      transportedCarrier⟩

theorem CollisionKernelCarrier_matrix_readback_totality [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance name matrixRead terminal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance name
        bundle pkg ->
      Cont ledger matrix matrixRead ->
        Cont matrixRead name terminal ->
          PkgSig bundle terminal pkg ->
            UnaryHistory window ∧ UnaryHistory fold ∧ UnaryHistory ledger ∧
              UnaryHistory matrix ∧ UnaryHistory matrixRead ∧ UnaryHistory terminal ∧
                Cont ledger matrix matrixRead ∧ Cont matrixRead name terminal ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier matrixReadRoute terminalRoute terminalPkg
  obtain ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, _momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, nameUnary, _windowRoute, _ledgerShadow,
    _momentShadow, provenancePkg, _namePkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixReadRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed matrixReadUnary nameUnary terminalRoute
  exact
    ⟨windowUnary, foldUnary, ledgerUnary, matrixUnary, matrixReadUnary, terminalUnary,
      matrixReadRoute, terminalRoute, provenancePkg, terminalPkg⟩

theorem CollisionKernelCarrier_fiber_classifier_composition [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert matrixRead
      shadowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont ledger matrix matrixRead ->
        Cont matrixRead shadow shadowRead ->
          UnaryHistory matrixRead ∧ UnaryHistory shadowRead ∧
            Cont ledger matrix matrixRead ∧ Cont matrixRead shadow shadowRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg
  intro carrier matrixRoute shadowRoute
  obtain ⟨_windowUnary, _foldUnary, ledgerUnary, matrixUnary, _momentUnary, shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowRoute,
    _ledgerRoute, _momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixRoute
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed matrixReadUnary shadowUnary shadowRoute
  exact
    ⟨matrixReadUnary, shadowReadUnary, matrixRoute, shadowRoute, provenancePkg,
      nameCertPkg⟩

theorem CollisionKernelCarrier_downstream_non_escape_package [AskSetup] [PackageSetup]
    {window fold ledger matrix moment shadow transport route provenance nameCert matrixRead
      shadowRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CollisionKernelCarrier window fold ledger matrix moment shadow transport route provenance
        nameCert bundle pkg ->
      Cont ledger matrix matrixRead ->
        Cont moment matrix shadowRead ->
          Cont matrixRead nameCert terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory matrixRead ∧ UnaryHistory shadowRead ∧ UnaryHistory terminal ∧
                Cont ledger matrix matrixRead ∧ Cont moment matrix shadowRead ∧
                  Cont matrixRead nameCert terminal ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle nameCert pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier matrixReadRoute shadowReadRoute terminalRoute terminalPkg
  obtain ⟨_windowUnary, _foldUnary, ledgerUnary, matrixUnary, momentUnary, _shadowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, nameCertUnary, _windowRoute,
    _ledgerRoute, _momentRoute, provenancePkg, nameCertPkg⟩ := carrier
  have matrixReadUnary : UnaryHistory matrixRead :=
    unary_cont_closed ledgerUnary matrixUnary matrixReadRoute
  have shadowReadUnary : UnaryHistory shadowRead :=
    unary_cont_closed momentUnary matrixUnary shadowReadRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed matrixReadUnary nameCertUnary terminalRoute
  exact
    ⟨matrixReadUnary, shadowReadUnary, terminalUnary, matrixReadRoute, shadowReadRoute,
      terminalRoute, provenancePkg, nameCertPkg, terminalPkg⟩

end BEDC.Derived.CollisionKernelUp
