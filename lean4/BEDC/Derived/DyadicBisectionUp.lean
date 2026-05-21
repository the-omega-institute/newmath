import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicBisectionCarrier [AskSetup] [PackageSetup]
    (initial precision midpoint branch nested endpoint regseq stream real transport route
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory initial ∧ UnaryHistory precision ∧ UnaryHistory midpoint ∧
    UnaryHistory branch ∧ UnaryHistory nested ∧ UnaryHistory endpoint ∧
      UnaryHistory regseq ∧ UnaryHistory stream ∧ UnaryHistory real ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory name ∧
          Cont initial precision midpoint ∧ Cont midpoint branch nested ∧
            Cont nested endpoint regseq ∧ Cont regseq stream real ∧
              Cont real transport route ∧ PkgSig bundle route pkg ∧
                PkgSig bundle name pkg

theorem DyadicBisectionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route
      name : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        (fun row : BHist =>
          DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq
            stream real transport route name bundle pkg ∧ hsame row real)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro real (And.intro carrier (hsame_refl real))
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

theorem DyadicBisectionCarrier_branch_endpoint_transport [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route
      name initial' precision' midpoint' branch' nested' endpoint' regseq' stream' real'
      transport' route' name' : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      hsame initial initial' -> hsame precision precision' -> hsame midpoint midpoint' ->
        hsame branch branch' -> hsame nested nested' -> hsame endpoint endpoint' ->
          hsame regseq regseq' -> hsame stream stream' -> hsame real real' ->
            hsame transport transport' -> hsame route route' -> hsame name name' ->
              DyadicBisectionCarrier initial' precision' midpoint' branch' nested' endpoint'
                  regseq' stream' real' transport' route' name' bundle pkg ∧
                hsame endpoint endpoint' ∧ hsame regseq regseq' ∧ hsame stream stream' ∧
                  hsame real real' := by
  intro carrier sameInitial samePrecision sameMidpoint sameBranch sameNested sameEndpoint
    sameRegseq sameStream sameReal sameTransport sameRoute sameName
  cases sameInitial
  cases samePrecision
  cases sameMidpoint
  cases sameBranch
  cases sameNested
  cases sameEndpoint
  cases sameRegseq
  cases sameStream
  cases sameReal
  cases sameTransport
  cases sameRoute
  cases sameName
  exact And.intro carrier
    (And.intro (hsame_refl endpoint)
      (And.intro (hsame_refl regseq)
        (And.intro (hsame_refl stream) (hsame_refl real))))

theorem DyadicBisectionCarrier_branch_nested_window_scope [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected realSeal : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont branch nested selected ->
        Cont selected endpoint realSeal ->
          PkgSig bundle route pkg ->
            UnaryHistory selected ∧ UnaryHistory realSeal ∧
              hsame selected (append branch nested) ∧
                hsame realSeal (append selected endpoint) ∧ PkgSig bundle route pkg := by
  intro carrier selectedRow realSealRow routeSig
  have branchUnary : UnaryHistory branch := carrier.right.right.right.left
  have nestedUnary : UnaryHistory nested := carrier.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint := carrier.right.right.right.right.right.left
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed branchUnary nestedUnary selectedRow
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed selectedUnary endpointUnary realSealRow
  exact And.intro selectedUnary
      (And.intro realSealUnary
        (And.intro selectedRow (And.intro realSealRow routeSig)))

theorem DyadicBisectionCarrier_nested_interval_bridge [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont midpoint branch selected ->
        UnaryHistory selected ∧ hsame selected (append midpoint branch) ∧ UnaryHistory nested ∧
          PkgSig bundle route pkg := by
  intro carrier selectedRow
  obtain ⟨_initialUnary, _precisionUnary, midpointUnary, branchUnary, nestedUnary,
    _endpointUnary, _regseqUnary, _streamUnary, _realUnary, _transportUnary, _routeUnary,
    _nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, routePkg, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed midpointUnary branchUnary selectedRow
  exact ⟨selectedUnary, selectedRow, nestedUnary, routePkg⟩

theorem DyadicBisectionCarrier_real_stream_endpoint_scope [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      retained sealRow : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont nested endpoint retained ->
        Cont retained stream sealRow ->
          PkgSig bundle sealRow pkg ->
            UnaryHistory retained ∧ UnaryHistory sealRow ∧
              hsame retained (append nested endpoint) ∧
                hsame sealRow (append retained stream) ∧
                  Cont nested endpoint retained ∧ Cont retained stream sealRow ∧
                    PkgSig bundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier retainedRow sealRowRoute sealSig
  obtain ⟨_initialUnary, _precisionUnary, _midpointUnary, _branchUnary, nestedUnary,
    endpointUnary, _regseqUnary, streamUnary, _realUnary, _transportUnary, _routeUnary,
    _nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, _routePkg, _namePkg⟩ := carrier
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed nestedUnary endpointUnary retainedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed retainedUnary streamUnary sealRowRoute
  exact
    ⟨retainedUnary, sealUnary, retainedRow, sealRowRoute, retainedRow, sealRowRoute, sealSig⟩

theorem DyadicBisectionCarrier_retained_interval_nonempty_iff [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected retained : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont branch nested selected ->
        Cont selected endpoint retained ->
          UnaryHistory retained ∧
            (((hsame retained BHist.Empty -> False) ↔
                (hsame selected BHist.Empty -> False) ∨
                  (hsame endpoint BHist.Empty -> False))) ∧
              PkgSig bundle route pkg := by
  intro carrier selectedRow retainedRow
  obtain ⟨_initialUnary, _precisionUnary, _midpointUnary, branchUnary, nestedUnary,
    endpointUnary, _regseqUnary, _streamUnary, _realUnary, _transportUnary, _routeUnary,
    _nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, routePkg, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed branchUnary nestedUnary selectedRow
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed selectedUnary endpointUnary retainedRow
  have retainedNonempty :
      ((hsame retained BHist.Empty -> False) ↔
        (hsame selected BHist.Empty -> False) ∨
          (hsame endpoint BHist.Empty -> False)) := by
    cases retainedRow
    exact append_nonempty_iff
  exact ⟨retainedUnary, retainedNonempty, routePkg⟩

theorem DyadicBisectionCarrier_nested_window_handoff [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected retained sealRow : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont branch nested selected ->
        Cont selected endpoint retained ->
          Cont retained stream sealRow ->
            PkgSig bundle sealRow pkg ->
              UnaryHistory selected /\ UnaryHistory retained /\ UnaryHistory sealRow /\
                hsame selected (append branch nested) /\
                  hsame retained (append selected endpoint) /\
                    hsame sealRow (append retained stream) /\
                      PkgSig bundle route pkg /\ PkgSig bundle sealRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedRow retainedRow sealRoute sealSig
  obtain ⟨_initialUnary, _precisionUnary, _midpointUnary, branchUnary, nestedUnary,
    endpointUnary, _regseqUnary, streamUnary, _realUnary, _transportUnary, _routeUnary,
    _nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, routePkg, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed branchUnary nestedUnary selectedRow
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed selectedUnary endpointUnary retainedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed retainedUnary streamUnary sealRoute
  exact
    ⟨selectedUnary, retainedUnary, sealUnary, selectedRow, retainedRow, sealRoute, routePkg,
      sealSig⟩

theorem DyadicBisectionCarrier_public_branch_totality [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected retained sealRow publicRoute : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont branch nested selected ->
        Cont selected endpoint retained ->
          Cont retained stream sealRow ->
            Cont sealRow name publicRoute ->
              PkgSig bundle sealRow pkg ->
                PkgSig bundle publicRoute pkg ->
                  UnaryHistory retained ∧ UnaryHistory sealRow ∧ UnaryHistory publicRoute ∧
                    hsame selected (append branch nested) ∧
                      hsame retained (append selected endpoint) ∧
                        hsame sealRow (append retained stream) ∧
                          Cont sealRow name publicRoute ∧ PkgSig bundle route pkg ∧
                            PkgSig bundle publicRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedRow retainedRow sealRoute publicRouteRow _sealSig publicRouteSig
  obtain ⟨_initialUnary, _precisionUnary, _midpointUnary, branchUnary, nestedUnary,
    endpointUnary, _regseqUnary, streamUnary, _realUnary, _transportUnary, _routeUnary,
    nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, routePkg, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed branchUnary nestedUnary selectedRow
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed selectedUnary endpointUnary retainedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed retainedUnary streamUnary sealRoute
  have publicRouteUnary : UnaryHistory publicRoute :=
    unary_cont_closed sealUnary nameUnary publicRouteRow
  exact
    ⟨retainedUnary, sealUnary, publicRouteUnary, selectedRow, retainedRow, sealRoute,
      publicRouteRow, routePkg, publicRouteSig⟩

theorem DyadicBisectionCarrier_retained_interval_consumer_route [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {initial precision midpoint branch nested endpoint regseq stream real transport route name
      selected retained sealRow publicRoute publicRoute' : BHist} :
    DyadicBisectionCarrier initial precision midpoint branch nested endpoint regseq stream real
        transport route name bundle pkg ->
      Cont branch nested selected ->
        Cont selected endpoint retained ->
          Cont retained stream sealRow ->
            Cont sealRow name publicRoute ->
              Cont sealRow name publicRoute' ->
                PkgSig bundle publicRoute pkg ->
                  PkgSig bundle publicRoute' pkg ->
                    hsame publicRoute publicRoute' ∧ UnaryHistory publicRoute ∧
                      UnaryHistory publicRoute' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier selectedRow retainedRow sealRoute publicRouteRow publicRouteRow'
    _publicRouteSig _publicRouteSig'
  obtain ⟨_initialUnary, _precisionUnary, _midpointUnary, branchUnary, nestedUnary,
    endpointUnary, _regseqUnary, streamUnary, _realUnary, _transportUnary, _routeUnary,
    nameUnary, _initialPrecision, _midpointBranch, _nestedEndpoint, _regseqStream,
    _realTransport, _routePkg, _namePkg⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed branchUnary nestedUnary selectedRow
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed selectedUnary endpointUnary retainedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed retainedUnary streamUnary sealRoute
  have publicRouteUnary : UnaryHistory publicRoute :=
    unary_cont_closed sealUnary nameUnary publicRouteRow
  have publicRouteUnary' : UnaryHistory publicRoute' :=
    unary_cont_closed sealUnary nameUnary publicRouteRow'
  have samePublicRoute : hsame publicRoute publicRoute' :=
    cont_respects_hsame (hsame_refl sealRow) (hsame_refl name) publicRouteRow publicRouteRow'
  exact ⟨samePublicRoute, publicRouteUnary, publicRouteUnary'⟩

end BEDC.Derived.DyadicBisectionUp
