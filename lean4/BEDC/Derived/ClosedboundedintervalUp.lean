import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalPacket [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ UnaryHistory exported ∧ Cont lower upper order ∧
          Cont order rational dyadic ∧ Cont stream readback sealRow ∧
            Cont transport replay provenance ∧ Cont provenance localName exported ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem ClosedBoundedIntervalPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
              transport replay provenance localName exported bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro packet (hsame_refl localName))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem ClosedBoundedIntervalPacket_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg)
    {lower' upper' order' : BHist}
    (hl : hsame lower lower') (hu : hsame upper upper')
    (horder' : Cont lower' upper' order') : hsame order order' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  cases hl
  cases hu
  exact
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
      horder'.symm

theorem ClosedBoundedIntervalPacket_root_source_split [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg) :
    hsame dyadic (append (append lower upper) rational) ∧
      hsame sealRow (append stream readback) ∧
        hsame exported (append (append transport replay) localName) := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  constructor
  · exact
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
        (congrArg (fun row : BHist => append row rational)
          packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left)
  · constructor
    · exact
        packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
    · exact
        packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
          (congrArg (fun row : BHist => append row localName)
            packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left)

theorem ClosedBoundedIntervalPacket_scoped_kernel_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg) :
    UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
      UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
        UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
          UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont lower upper order ∧
            Cont order rational dyadic ∧ Cont stream readback sealRow ∧
              Cont transport replay provenance ∧ Cont provenance localName exported ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, transportUnary, replayUnary, provenanceUnary,
    localNameUnary, _exportedUnary, endpointRoute, containmentRoute, sealRowRoute,
    replayRoute, nameRoute, provenancePkg, localNamePkg⟩ := packet
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, transportUnary, replayUnary, provenanceUnary,
      localNameUnary, endpointRoute, containmentRoute, sealRowRoute, replayRoute, nameRoute,
      provenancePkg, localNamePkg⟩

theorem ClosedBoundedIntervalPacket_endpoint_containment_route [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg)
    {containmentRead finiteNet : BHist} (containmentUnary : UnaryHistory containmentRead)
    (netRoute : Cont dyadic containmentRead finiteNet) :
    hsame order (append lower upper) ∧ hsame dyadic (append (append lower upper) rational) ∧
      UnaryHistory finiteNet ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  constructor
  · exact packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  · constructor
    · exact
        packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left.trans
          (congrArg (fun row : BHist => append row rational)
            packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left)
    · constructor
      · exact
          unary_cont_closed
            packet.right.right.right.right.left
            containmentUnary
            netRoute
      · exact
          ⟨packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
            packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem ClosedBoundedIntervalPacket_root_containment_split [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet : ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback
      sealRow transport replay provenance localName exported bundle pkg) :
    hsame order (append lower upper) ∧
      hsame dyadic (append (append lower upper) rational) ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, endpointRoute,
    containmentRoute, _sealRowRoute, _replayRoute, _nameRoute, provenancePkg,
    localNamePkg⟩ := packet
  exact
    ⟨endpointRoute,
      containmentRoute.trans (congrArg (fun row : BHist => append row rational) endpointRoute),
      transportUnary, replayUnary, provenancePkg, localNamePkg⟩

theorem ClosedBoundedIntervalPacket_root_obligation_spine [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported endpointSource containmentSource sealSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont lower upper endpointSource ->
        Cont rational dyadic containmentSource ->
          Cont stream readback sealSource ->
            PkgSig bundle endpointSource pkg ->
              PkgSig bundle containmentSource pkg ->
                PkgSig bundle sealSource pkg ->
                  UnaryHistory endpointSource ∧ UnaryHistory containmentSource ∧
                    UnaryHistory sealSource ∧ Cont lower upper endpointSource ∧
                      Cont rational dyadic containmentSource ∧ Cont stream readback sealSource ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpointSource pkg ∧
                          PkgSig bundle containmentSource pkg ∧ PkgSig bundle sealSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet endpointRoute containmentRoute sealRoute endpointPkg containmentPkg sealPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _carrierEndpointRoute, _carrierContainmentRoute,
    _carrierSealRoute, _carrierReplayRoute, _carrierNameRoute, provenancePkg, _localNamePkg⟩ :=
      packet
  have endpointUnary : UnaryHistory endpointSource :=
    unary_cont_closed lowerUnary upperUnary endpointRoute
  have containmentUnary : UnaryHistory containmentSource :=
    unary_cont_closed rationalUnary dyadicUnary containmentRoute
  have sealUnary : UnaryHistory sealSource :=
    unary_cont_closed streamUnary readbackUnary sealRoute
  exact
    ⟨endpointUnary, containmentUnary, sealUnary, endpointRoute, containmentRoute, sealRoute,
      provenancePkg, endpointPkg, containmentPkg, sealPkg⟩

theorem ClosedBoundedIntervalPacket_root_seal_split [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont stream readback sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
            UnaryHistory sealRead ∧ Cont stream readback sealRow ∧
              Cont stream readback sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet sealReadRoute sealReadPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute,
    _containmentRoute, sealRowRoute, _replayRoute, _nameRoute, provenancePkg,
    localNamePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed streamUnary readbackUnary sealReadRoute
  exact
    ⟨streamUnary, readbackUnary, sealRowUnary, sealReadUnary, sealRowRoute, sealReadRoute,
      provenancePkg, localNamePkg, sealReadPkg⟩

theorem ClosedBoundedIntervalPacket_finite_cover_window_exactness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverWindow coverCell refinement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory coverWindow ->
        Cont exported coverWindow coverCell ->
          Cont coverCell dyadic refinement ->
            PkgSig bundle refinement pkg ->
              UnaryHistory exported ∧ UnaryHistory coverWindow ∧ UnaryHistory coverCell ∧
                UnaryHistory refinement ∧ Cont exported coverWindow coverCell ∧
                  Cont coverCell dyadic refinement ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle refinement pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet coverWindowUnary coverCellRoute refinementRoute refinementPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed exportedUnary coverWindowUnary coverCellRoute
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed coverCellUnary dyadicUnary refinementRoute
  exact
    ⟨exportedUnary, coverWindowUnary, coverCellUnary, refinementUnary, coverCellRoute,
      refinementRoute, provenancePkg, localNamePkg, refinementPkg⟩

theorem ClosedBoundedIntervalPacket_net_consumer_readiness [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported mesh modulus nesting ready : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory mesh ->
        UnaryHistory nesting ->
          Cont exported mesh modulus ->
            Cont modulus nesting ready ->
              PkgSig bundle ready pkg ->
                UnaryHistory exported ∧ UnaryHistory mesh ∧ UnaryHistory modulus ∧
                  UnaryHistory nesting ∧ UnaryHistory ready ∧ Cont exported mesh modulus ∧
                    Cont modulus nesting ready ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle ready pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet meshUnary nestingUnary modulusRoute readyRoute readyPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed exportedUnary meshUnary modulusRoute
  have readyUnary : UnaryHistory ready :=
    unary_cont_closed modulusUnary nestingUnary readyRoute
  exact
    ⟨exportedUnary, meshUnary, modulusUnary, nestingUnary, readyUnary, modulusRoute,
      readyRoute, provenancePkg, localNamePkg, readyPkg⟩

theorem ClosedBoundedIntervalPacket_carrier_gate [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported intervalNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont exported dyadic intervalNetRead →
        PkgSig bundle intervalNetRead pkg →
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
            UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory exported ∧
                UnaryHistory intervalNetRead ∧ Cont exported dyadic intervalNetRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle intervalNetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet intervalNetRoute intervalNetPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have intervalNetUnary : UnaryHistory intervalNetRead :=
    unary_cont_closed exportedUnary dyadicUnary intervalNetRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, exportedUnary, intervalNetUnary, intervalNetRoute,
      provenancePkg, intervalNetPkg⟩

theorem ClosedBoundedIntervalPacket_source_transport [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sourceWindow sourceRead sourceOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory sourceWindow ->
        Cont exported sourceWindow sourceRead ->
          Cont sourceRead provenance sourceOut ->
            PkgSig bundle sourceOut pkg ->
              UnaryHistory exported ∧ UnaryHistory sourceWindow ∧ UnaryHistory sourceRead ∧
                UnaryHistory sourceOut ∧ Cont exported sourceWindow sourceRead ∧
                  Cont sourceRead provenance sourceOut ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle sourceOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet sourceWindowUnary sourceReadRoute sourceOutRoute sourceOutPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed exportedUnary sourceWindowUnary sourceReadRoute
  have sourceOutUnary : UnaryHistory sourceOut :=
    unary_cont_closed sourceReadUnary provenanceUnary sourceOutRoute
  exact
    ⟨exportedUnary, sourceWindowUnary, sourceReadUnary, sourceOutUnary, sourceReadRoute,
      sourceOutRoute, provenancePkg, localNamePkg, sourceOutPkg⟩

theorem ClosedBoundedIntervalPacket_source_nonescape [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance localName
      exported sourceWindow sourceRead sourceOut netRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory sourceWindow ->
        Cont exported sourceWindow sourceRead ->
          Cont sourceRead provenance sourceOut ->
            Cont sourceOut dyadic netRead ->
              Cont netRead replay compactRead ->
                PkgSig bundle compactRead pkg ->
                  UnaryHistory sourceRead ∧ UnaryHistory sourceOut ∧ UnaryHistory netRead ∧
                    UnaryHistory compactRead ∧ Cont exported sourceWindow sourceRead ∧
                      Cont sourceRead provenance sourceOut ∧ Cont sourceOut dyadic netRead ∧
                        Cont netRead replay compactRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle localName pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet sourceWindowUnary sourceReadRoute sourceOutRoute netReadRoute compactRoute
    compactPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, replayUnary,
    provenanceUnary, _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed exportedUnary sourceWindowUnary sourceReadRoute
  have sourceOutUnary : UnaryHistory sourceOut :=
    unary_cont_closed sourceReadUnary provenanceUnary sourceOutRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed sourceOutUnary dyadicUnary netReadRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed netReadUnary replayUnary compactRoute
  exact
    ⟨sourceReadUnary, sourceOutUnary, netReadUnary, compactReadUnary, sourceReadRoute,
      sourceOutRoute, netReadRoute, compactRoute, provenancePkg, localNamePkg, compactPkg⟩

theorem ClosedBoundedIntervalPacket_dyadic_net_ledger [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteNet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream finiteNet ->
        PkgSig bundle finiteNet pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
            UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory finiteNet ∧
              Cont order rational dyadic ∧ Cont dyadic stream finiteNet ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle finiteNet pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet finiteNetRoute finiteNetPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, dyadicRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed dyadicUnary streamUnary finiteNetRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, finiteNetUnary,
      dyadicRoute, finiteNetRoute, provenancePkg, localNamePkg, finiteNetPkg⟩

theorem ClosedBoundedIntervalPacket_finite_net_source [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteNet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream finiteNet ->
        PkgSig bundle finiteNet pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row finiteNet ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
                hsame row dyadic ∨ Cont dyadic stream finiteNet)
            (fun row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle finiteNet pkg ∧
                hsame row finiteNet)
            hsame ∧
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory finiteNet ∧
                Cont lower upper order ∧ Cont order rational dyadic ∧
                  Cont dyadic stream finiteNet ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle finiteNet pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet finiteNetRoute finiteNetPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, dyadicRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed dyadicUnary streamUnary finiteNetRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row finiteNet ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
            hsame row dyadic ∨ Cont dyadic stream finiteNet)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle finiteNet pkg ∧ hsame row finiteNet)
        hsame := {
    core := {
      carrier_inhabited :=
        ⟨finiteNet, hsame_refl finiteNet, finiteNetUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' left right
        exact hsame_trans left right
      carrier_respects_equiv := by
        intro row other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr finiteNetRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, finiteNetPkg, source.left⟩
  }
  exact
    ⟨cert, lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, finiteNetUnary,
      endpointRoute, dyadicRoute, finiteNetRoute, provenancePkg, localNamePkg, finiteNetPkg⟩

theorem ClosedBoundedIntervalPacket_root_unblock_obligations [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteNet locatedCover nestedWindow compactUniform : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported dyadic finiteNet ->
        Cont exported stream locatedCover ->
          Cont exported readback nestedWindow ->
            Cont exported sealRow compactUniform ->
              PkgSig bundle finiteNet pkg ->
                PkgSig bundle locatedCover pkg ->
                  PkgSig bundle nestedWindow pkg ->
                    PkgSig bundle compactUniform pkg ->
                      UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
                        UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                          UnaryHistory readback ∧ UnaryHistory sealRow ∧
                            UnaryHistory exported ∧ UnaryHistory finiteNet ∧
                              UnaryHistory locatedCover ∧ UnaryHistory nestedWindow ∧
                                UnaryHistory compactUniform ∧ Cont exported dyadic finiteNet ∧
                                  Cont exported stream locatedCover ∧
                                    Cont exported readback nestedWindow ∧
                                      Cont exported sealRow compactUniform ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg ∧
                                            PkgSig bundle compactUniform pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet finiteNetRoute locatedCoverRoute nestedWindowRoute compactUniformRoute
    _finiteNetPkg _locatedCoverPkg _nestedWindowPkg compactUniformPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed exportedUnary dyadicUnary finiteNetRoute
  have locatedCoverUnary : UnaryHistory locatedCover :=
    unary_cont_closed exportedUnary streamUnary locatedCoverRoute
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed exportedUnary readbackUnary nestedWindowRoute
  have compactUniformUnary : UnaryHistory compactUniform :=
    unary_cont_closed exportedUnary sealRowUnary compactUniformRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, exportedUnary, finiteNetUnary, locatedCoverUnary,
      nestedWindowUnary, compactUniformUnary, finiteNetRoute, locatedCoverRoute,
      nestedWindowRoute, compactUniformRoute, provenancePkg, localNamePkg, compactUniformPkg⟩

theorem ClosedBoundedIntervalPacket_nested_window_factorization [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported nestedWindow nestedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported readback nestedWindow ->
        Cont nestedWindow sealRow nestedSeal ->
          PkgSig bundle nestedSeal pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory nestedWindow ∧
                UnaryHistory nestedSeal ∧ Cont exported readback nestedWindow ∧
                  Cont nestedWindow sealRow nestedSeal ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle nestedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet nestedWindowRoute nestedSealRoute nestedSealPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, _dyadicUnary, _streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have nestedWindowUnary : UnaryHistory nestedWindow :=
    unary_cont_closed exportedUnary readbackUnary nestedWindowRoute
  have nestedSealUnary : UnaryHistory nestedSeal :=
    unary_cont_closed nestedWindowUnary sealRowUnary nestedSealRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, readbackUnary, sealRowUnary, nestedWindowUnary,
      nestedSealUnary, nestedWindowRoute, nestedSealRoute, provenancePkg, localNamePkg,
      nestedSealPkg⟩

theorem ClosedBoundedIntervalPacket_located_endpoint_grid [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported grid cell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont order dyadic grid ->
        Cont grid stream cell ->
          PkgSig bundle cell pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory grid ∧
                UnaryHistory cell ∧ Cont order dyadic grid ∧ Cont grid stream cell ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle cell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet gridRoute cellRoute cellPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have gridUnary : UnaryHistory grid :=
    unary_cont_closed orderUnary dyadicUnary gridRoute
  have cellUnary : UnaryHistory cell :=
    unary_cont_closed gridUnary streamUnary cellRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, dyadicUnary, streamUnary, gridUnary, cellUnary,
      gridRoute, cellRoute, provenancePkg, localNamePkg, cellPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
