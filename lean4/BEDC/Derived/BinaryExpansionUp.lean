import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BinaryExpansionPacket [AskSetup] [PackageSetup]
    (digits windows approximation regular realSeal transport route provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
          Cont transport route provenance ∧ PkgSig bundle provenance pkg

theorem BinaryExpansionPacket_prefix_window_stability [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert digits'
      windows' approximation' regular' realSeal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      hsame windows windows' -> hsame digits digits' -> hsame regular regular' ->
        Cont windows' digits' approximation' -> Cont approximation' regular' realSeal' ->
          BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport
              route provenance nameCert bundle pkg ∧
            hsame approximation approximation' ∧ hsame realSeal realSeal' := by
  intro packet sameWindows sameDigits sameRegular approximationRow' realSealRow'
  have approximationRow : Cont windows digits approximation :=
    packet.right.right.right.right.right.right.right.right.right.left
  have realSealRow : Cont approximation regular realSeal :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have sameApproximation : hsame approximation approximation' :=
    cont_respects_hsame sameWindows sameDigits approximationRow approximationRow'
  have sameRealSeal : hsame realSeal realSeal' :=
    cont_respects_hsame sameApproximation sameRegular realSealRow realSealRow'
  have transported :
      BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport route
        provenance nameCert bundle pkg :=
    ⟨unary_transport packet.left sameDigits,
      unary_transport packet.right.left sameWindows,
      unary_transport packet.right.right.left sameApproximation,
      unary_transport packet.right.right.right.left sameRegular,
      unary_transport packet.right.right.right.right.left sameRealSeal,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      approximationRow',
      realSealRow',
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right⟩
  exact ⟨transported, sameApproximation, sameRealSeal⟩

theorem BinaryExpansionPacket_regular_handoff_factorization [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      handoffRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      hsame handoffRoute (append windows realSeal) →
        hsame handoffRoute (append windows (append approximation regular)) ∧
          Cont windows digits approximation ∧
            Cont approximation regular realSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet handoffWindowsSeal
  obtain ⟨_digitsUnary, _windowsUnary, _approximationUnary, _regularUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigits,
    approximationRegular, _transportRoute, pkgSig⟩ := packet
  have realSealSame : hsame realSeal (append approximation regular) := approximationRegular
  have handoffSame :
      hsame (append windows realSeal) (append windows (append approximation regular)) :=
    congrArg (fun row => append windows row) realSealSame
  exact ⟨hsame_trans handoffWindowsSeal handoffSame, windowsDigits, approximationRegular, pkgSig⟩

theorem BinaryExpansionPacket_real_readback_boundary [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      Cont regular realSeal realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory windows ∧ UnaryHistory digits ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory realRead ∧
              Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
                Cont regular realSeal realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet regularRealSealRead realReadPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigitsApproximation,
    approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary realSealUnary regularRealSealRead
  exact
    ⟨windowsUnary, digitsUnary, approximationUnary, regularUnary, realSealUnary,
      realReadUnary, windowsDigitsApproximation, approximationRegularRealSeal,
      regularRealSealRead, provenancePkg, realReadPkg⟩

theorem BinaryExpansionPacket_real_seal_prefix_coherence [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      prefixRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont windows digits prefixRead →
        Cont prefixRead regular regularRead →
          Cont regularRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory windows ∧ UnaryHistory digits ∧ UnaryHistory prefixRead ∧
                UnaryHistory regularRead ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
                  Cont windows digits prefixRead ∧ Cont prefixRead regular regularRead ∧
                    Cont regularRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsDigitsPrefix prefixRegularRead regularReadSeal sealReadPkg
  obtain ⟨digitsUnary, windowsUnary, _approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowsDigitsApproximation,
    _approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed windowsUnary digitsUnary windowsDigitsPrefix
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed prefixReadUnary regularUnary prefixRegularRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary realSealUnary regularReadSeal
  exact
    ⟨windowsUnary, digitsUnary, prefixReadUnary, regularReadUnary, realSealUnary,
      sealReadUnary, windowsDigitsPrefix, prefixRegularRead, regularReadSeal, provenancePkg,
      sealReadPkg⟩

theorem BinaryExpansionPacket_dyadic_ledger_exhaustion [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont digits windows dyadicRead →
        PkgSig bundle dyadicRead pkg →
          UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory dyadicRead ∧
              Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
                Cont digits windows dyadicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet digitsWindowsRead dyadicReadPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigitsApproximation,
    approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed digitsUnary windowsUnary digitsWindowsRead
  exact
    ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
      dyadicReadUnary, windowsDigitsApproximation, approximationRegularRealSeal,
      digitsWindowsRead, provenancePkg, dyadicReadPkg⟩

theorem BinaryExpansionPacket_scoped_dependency_factorization [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont windows approximation scopedRead →
        PkgSig bundle scopedRead pkg →
          UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory scopedRead ∧
              Cont windows digits approximation ∧ Cont approximation regular realSeal ∧
                Cont windows approximation scopedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsApproximationScoped scopedReadPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    windowsDigitsApproximation, approximationRegularRealSeal, _transportRouteProvenance,
    provenancePkg⟩ := packet
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed windowsUnary approximationUnary windowsApproximationScoped
  exact
    ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
      scopedReadUnary, windowsDigitsApproximation, approximationRegularRealSeal,
      windowsApproximationScoped, provenancePkg, scopedReadPkg⟩

theorem BinaryExpansionPacket_prefix_tail_radius_monotonicity [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert prefixRow
      extendedPrefix tailRoute oldRadius newRadius : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg ->
      UnaryHistory prefixRow ->
        UnaryHistory tailRoute ->
          hsame extendedPrefix (append prefixRow tailRoute) ->
            Cont windows prefixRow oldRadius ->
              Cont windows extendedPrefix newRadius ->
                PkgSig bundle oldRadius pkg ->
                  PkgSig bundle newRadius pkg ->
                    UnaryHistory windows ∧ UnaryHistory prefixRow ∧ UnaryHistory extendedPrefix ∧
                      UnaryHistory oldRadius ∧ UnaryHistory newRadius ∧
                        hsame extendedPrefix (append prefixRow tailRoute) ∧
                          Cont windows prefixRow oldRadius ∧
                            Cont windows extendedPrefix newRadius ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle oldRadius pkg ∧
                                PkgSig bundle newRadius pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro packet prefixUnary tailUnary sameExtended windowsPrefixOld windowsExtendedNew
    oldRadiusPkg newRadiusPkg
  obtain ⟨_digitsUnary, windowsUnary, _approximationUnary, _regularUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowsDigitsApproximation,
    _approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have appendUnary : UnaryHistory (append prefixRow tailRoute) :=
    unary_append_closed prefixUnary tailUnary
  have extendedUnary : UnaryHistory extendedPrefix :=
    unary_transport_symm appendUnary sameExtended
  have oldRadiusUnary : UnaryHistory oldRadius :=
    unary_cont_closed windowsUnary prefixUnary windowsPrefixOld
  have newRadiusUnary : UnaryHistory newRadius :=
    unary_cont_closed windowsUnary extendedUnary windowsExtendedNew
  exact
    ⟨windowsUnary, prefixUnary, extendedUnary, oldRadiusUnary, newRadiusUnary, sameExtended,
      windowsPrefixOld, windowsExtendedNew, provenancePkg, oldRadiusPkg, newRadiusPkg⟩

theorem BinaryExpansionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
        (fun _row : BHist =>
          UnaryHistory digits ∧ UnaryHistory windows ∧ UnaryHistory approximation ∧
            UnaryHistory regular ∧ UnaryHistory realSeal ∧ Cont windows digits approximation ∧
              Cont approximation regular realSeal)
        (fun _row : BHist =>
          PkgSig bundle provenance pkg ∧ UnaryHistory provenance ∧ UnaryHistory nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
    _transportUnary, _routeUnary, provenanceUnary, nameCertUnary, windowsDigitsApproximation,
    approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert ⟨hsame_refl nameCert, nameCertUnary⟩
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
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, realSealUnary,
          windowsDigitsApproximation, approximationRegularRealSeal⟩
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, provenanceUnary, nameCertUnary⟩
  }

theorem BinaryExpansionPacket_dyadic_window_public_readiness [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert windowRead
      dyadicWindow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont windows digits windowRead →
        Cont windowRead approximation dyadicWindow →
          Cont dyadicWindow regular publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row windowRead ∨ hsame row dyadicWindow ∨ hsame row publicRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory dyadicWindow ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet windowsDigitsRead windowApproximationRead dyadicRegularPublic publicPkg
  obtain ⟨digitsUnary, windowsUnary, approximationUnary, regularUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowsDigitsApproximation,
    _approximationRegularRealSeal, _transportRouteProvenance, provenancePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary digitsUnary windowsDigitsRead
  have dyadicWindowUnary : UnaryHistory dyadicWindow :=
    unary_cont_closed windowReadUnary approximationUnary windowApproximationRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed dyadicWindowUnary regularUnary dyadicRegularPublic
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row windowRead ∨ hsame row dyadicWindow ∨ hsame row publicRead)
        (fun row : BHist => UnaryHistory row)
        (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (Or.inr (Or.inr (hsame_refl publicRead)))
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
        cases source with
        | inl sameWindow =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
        | inr tail =>
            cases tail with
            | inl sameDyadic =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))
            | inr samePublic =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameWindow =>
          exact unary_transport windowReadUnary (hsame_symm sameWindow)
      | inr tail =>
          cases tail with
          | inl sameDyadic =>
              exact unary_transport dyadicWindowUnary (hsame_symm sameDyadic)
          | inr samePublic =>
              exact unary_transport publicReadUnary (hsame_symm samePublic)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, publicPkg⟩
  }
  exact ⟨cert, windowReadUnary, dyadicWindowUnary, publicReadUnary⟩

theorem BinaryExpansionPacket_prefix_refinement_real_seal_determinacy [AskSetup]
    [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert digits'
      windows' approximation' regular' realSeal' commonWindow transportedDigits
      transportedApproximation leftSealRead rightSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      BinaryExpansionPacket digits' windows' approximation' regular' realSeal' transport route
        provenance nameCert bundle pkg →
        hsame commonWindow windows →
          hsame commonWindow windows' →
            hsame transportedDigits digits →
              hsame transportedDigits digits' →
                Cont commonWindow transportedDigits transportedApproximation →
                  Cont transportedApproximation regular leftSealRead →
                    Cont transportedApproximation regular' rightSealRead →
                      PkgSig bundle leftSealRead pkg →
                        PkgSig bundle rightSealRead pkg →
                          hsame approximation transportedApproximation ∧
                            hsame approximation' transportedApproximation ∧
                              UnaryHistory leftSealRead ∧ UnaryHistory rightSealRead ∧
                                Cont transportedApproximation regular leftSealRead ∧
                                  Cont transportedApproximation regular' rightSealRead ∧
                                    PkgSig bundle leftSealRead pkg ∧
                                      PkgSig bundle rightSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet packet' sameCommonWindow sameCommonWindow' sameTransportedDigits
    sameTransportedDigits' commonTransportedApprox leftSealRoute rightSealRoute leftSealPkg
    rightSealPkg
  obtain ⟨_digitsUnary, _windowsUnary, approximationUnary, regularUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, windowsDigitsApproximation,
    _approximationRegularRealSeal, _transportRouteProvenance, _provenancePkg⟩ := packet
  obtain ⟨_digitsUnary', _windowsUnary', approximationUnary', regularUnary', _realSealUnary',
    _transportUnary', _routeUnary', _provenanceUnary', _nameCertUnary',
    windowsDigitsApproximation', _approximationRegularRealSeal',
    _transportRouteProvenance', _provenancePkg'⟩ := packet'
  have sameWindows : hsame windows commonWindow := hsame_symm sameCommonWindow
  have sameDigits : hsame digits transportedDigits := hsame_symm sameTransportedDigits
  have sameWindows' : hsame windows' commonWindow := hsame_symm sameCommonWindow'
  have sameDigits' : hsame digits' transportedDigits := hsame_symm sameTransportedDigits'
  have sameApproximation : hsame approximation transportedApproximation :=
    cont_respects_hsame sameWindows sameDigits windowsDigitsApproximation commonTransportedApprox
  have sameApproximation' : hsame approximation' transportedApproximation :=
    cont_respects_hsame sameWindows' sameDigits' windowsDigitsApproximation'
      commonTransportedApprox
  have transportedApproximationUnary : UnaryHistory transportedApproximation :=
    unary_transport approximationUnary sameApproximation
  have transportedApproximationUnary' : UnaryHistory transportedApproximation :=
    unary_transport approximationUnary' sameApproximation'
  have leftSealUnary : UnaryHistory leftSealRead :=
    unary_cont_closed transportedApproximationUnary regularUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSealRead :=
    unary_cont_closed transportedApproximationUnary' regularUnary' rightSealRoute
  exact
    ⟨sameApproximation, sameApproximation', leftSealUnary, rightSealUnary, leftSealRoute,
      rightSealRoute, leftSealPkg, rightSealPkg⟩

end BEDC.Derived.BinaryExpansionUp
