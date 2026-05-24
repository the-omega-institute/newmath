import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionReflectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionReflectionPacket [AskSetup] [PackageSetup]
    (completion universal separated diagonal regular sealRow transport route package provenance
      cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory completion ∧ UnaryHistory universal ∧ UnaryHistory separated ∧
    UnaryHistory diagonal ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory package ∧
        UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont completion universal package ∧
          Cont transport route provenance ∧ PkgSig bundle cert pkg

def CompletionReflectionClassifier [AskSetup] [PackageSetup]
    (completion universal separated diagonal regular sealRow transport route package provenance cert
      completion' universal' separated' diagonal' regular' sealRow' transport' route' package'
      provenance' cert' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
      package provenance cert bundle pkg ∧
    CompletionReflectionPacket completion' universal' separated' diagonal' regular' sealRow'
        transport' route' package' provenance' cert' bundle pkg ∧
      hsame completion completion' ∧ hsame universal universal' ∧ hsame separated separated' ∧
        hsame diagonal diagonal' ∧ hsame regular regular' ∧ hsame sealRow sealRow' ∧
          hsame transport transport' ∧ hsame route route' ∧ hsame cert cert' ∧
            Cont completion' universal' package' ∧ Cont transport' route' provenance' ∧
              PkgSig bundle cert' pkg

theorem CompletionReflectionPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          UnaryHistory reflected ∧ UnaryHistory sealRow ∧ UnaryHistory completion ∧
            UnaryHistory separated ∧ hsame reflected sealRow ∧ Cont diagonal regular reflected ∧
              Cont completion universal package ∧ PkgSig bundle cert pkg := by
  intro packet reflectedRow reflectedSame
  obtain ⟨completionUnary, _universalUnary, separatedUnary, diagonalUnary, regularUnary,
    sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    packageRow, _provenanceRow, certSig⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary' : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  exact
    ⟨reflectedUnary, sealUnary', completionUnary, separatedUnary, reflectedSame,
      reflectedRow, packageRow, certSig⟩

theorem CompletionReflectionPacket_extension_reflects [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      extension : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont universal completion extension ->
        hsame extension package ->
          UnaryHistory universal ∧ UnaryHistory completion ∧ UnaryHistory separated ∧
            UnaryHistory diagonal ∧ UnaryHistory regular ∧ hsame extension package ∧
              Cont universal completion extension ∧ Cont completion universal package ∧
                PkgSig bundle cert pkg := by
  intro packet extensionRow extensionSame
  obtain ⟨completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    packageRow, _provenanceRow, certSig⟩ := packet
  exact
    ⟨universalUnary, completionUnary, separatedUnary, diagonalUnary, regularUnary,
      extensionSame, extensionRow, packageRow, certSig⟩

theorem CompletionReflectionPacket_consumer_scope [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              UnaryHistory reflected ∧ UnaryHistory sealRow ∧ UnaryHistory extension ∧
                UnaryHistory completion ∧ Cont diagonal regular reflected ∧
                  Cont universal completion extension ∧ PkgSig bundle cert pkg := by
  intro packet reflectedRow reflectedSame extensionRow extensionSame
  obtain ⟨completionUnary, universalUnary, _separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    _packageRow, _provenanceRow, certSig⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  exact
    ⟨reflectedUnary, sealUnary, extensionUnary, completionUnary, reflectedRow, extensionRow,
      certSig⟩

theorem CompletionReflectionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CompletionReflectionPacket completion universal separated diagonal regular sealRow transport
            route package provenance cert bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CompletionReflectionPacket completion universal separated diagonal regular sealRow transport
            route package provenance cert bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          CompletionReflectionPacket completion universal separated diagonal regular sealRow transport
            route package provenance cert bundle pkg ∧ hsame row sealRow ∧ PkgSig bundle cert pkg)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro packet (hsame_refl sealRow))
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
      exact And.intro source.left (And.intro source.right packet.right.right.right.right.right.right.right.right.right.right.right.right.right)
  }

theorem CompletionReflectionPacket_carrier_scope [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row cert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row completion ∨ hsame row universal ∨ hsame row separated ∨
              hsame row diagonal ∨ hsame row regular ∨ hsame row sealRow ∨
                hsame row transport ∨ hsame row route ∨ hsame row package ∨
                  hsame row provenance ∨ hsame row cert)
          (fun row : BHist => PkgSig bundle cert pkg ∧ hsame row cert)
          hsame ∧
        UnaryHistory completion ∧ UnaryHistory universal ∧ UnaryHistory separated ∧
          UnaryHistory diagonal ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
            UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory package ∧
              UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont completion universal package ∧
                Cont transport route provenance ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet
  obtain ⟨completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary,
    sealUnary, transportUnary, routeUnary, packageUnary, provenanceUnary, certUnary,
    packageRow, provenanceRow, certSig⟩ := packet
  have semantic :
      SemanticNameCert
        (fun row : BHist => hsame row cert ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row completion ∨ hsame row universal ∨ hsame row separated ∨
            hsame row diagonal ∨ hsame row regular ∨ hsame row sealRow ∨
              hsame row transport ∨ hsame row route ∨ hsame row package ∨
                hsame row provenance ∨ hsame row cert)
        (fun row : BHist => PkgSig bundle cert pkg ∧ hsame row cert)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro cert (And.intro (hsame_refl cert) certUnary)
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
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro row source
      exact And.intro certSig source.left
  }
  exact
    ⟨semantic, completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary,
      sealUnary, transportUnary, routeUnary, packageUnary, provenanceUnary, certUnary,
      packageRow, provenanceRow, certSig⟩

theorem CompletionReflectionPacket_provenance_route_scope [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance
      cert audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont route provenance audit ->
        PkgSig bundle audit pkg ->
          UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory audit ∧
            Cont transport route provenance ∧ Cont route provenance audit ∧
              PkgSig bundle cert pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet auditRow auditSig
  obtain ⟨_completionUnary, _universalUnary, _separatedUnary, _diagonalUnary, _regularUnary,
    _sealUnary, _transportUnary, routeUnary, _packageUnary, provenanceUnary, _certUnary,
    _packageRow, provenanceRow, certSig⟩ := packet
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routeUnary provenanceUnary auditRow
  exact
    ⟨routeUnary, provenanceUnary, auditUnary, provenanceRow, auditRow, certSig, auditSig⟩

theorem CompletionReflectionPacket_public_export [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              UnaryHistory completion /\ UnaryHistory universal /\ UnaryHistory separated /\
                UnaryHistory diagonal /\ UnaryHistory regular /\ UnaryHistory sealRow /\
                  UnaryHistory reflected /\ UnaryHistory extension /\
                    Cont completion universal package /\ Cont diagonal regular reflected /\
                      Cont universal completion extension /\ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet reflectedRow reflectedSame extensionRow _extensionSame
  obtain ⟨completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    packageRow, _provenanceRow, certSig⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  exact
    ⟨completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary, sealUnary,
      reflectedUnary, extensionUnary, packageRow, reflectedRow, extensionRow, certSig⟩

theorem CompletionReflectionPacket_stream_regseq_real_factor [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance
      cert reflected extension audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              Cont route provenance audit ->
                PkgSig bundle audit pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory regular ∧ UnaryHistory reflected ∧
                    UnaryHistory sealRow ∧ UnaryHistory extension ∧ UnaryHistory route ∧
                      UnaryHistory provenance ∧ UnaryHistory audit ∧
                        Cont diagonal regular reflected ∧ Cont universal completion extension ∧
                          Cont route provenance audit ∧ hsame reflected sealRow ∧
                            hsame extension package ∧ PkgSig bundle cert pkg ∧
                              PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet reflectedRow reflectedSame extensionRow extensionSame auditRow auditPkg
  obtain ⟨completionUnary, universalUnary, _separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, routeUnary, _packageUnary, provenanceUnary, _certUnary,
    _packageRow, _provenanceRow, certPkg⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routeUnary provenanceUnary auditRow
  exact
    ⟨diagonalUnary, regularUnary, reflectedUnary, sealUnary, extensionUnary, routeUnary,
      provenanceUnary, auditUnary, reflectedRow, extensionRow, auditRow, reflectedSame,
      extensionSame, certPkg, auditPkg⟩

theorem CompletionReflectionPacket_real_seal_extension_coherence [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension coherence : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              Cont reflected extension coherence ->
                hsame coherence provenance ->
                  UnaryHistory reflected ∧ UnaryHistory extension ∧ UnaryHistory coherence ∧
                    hsame reflected sealRow ∧ hsame extension package ∧
                      hsame coherence provenance ∧ Cont diagonal regular reflected ∧
                        Cont universal completion extension ∧ Cont reflected extension coherence ∧
                          PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet reflectedRow reflectedSame extensionRow extensionSame coherenceRow coherenceSame
  obtain ⟨completionUnary, universalUnary, _separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    _packageRow, _provenanceRow, certPkg⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  have coherenceUnary : UnaryHistory coherence :=
    unary_cont_closed reflectedUnary extensionUnary coherenceRow
  exact
    ⟨reflectedUnary, extensionUnary, coherenceUnary, reflectedSame, extensionSame,
      coherenceSame, reflectedRow, extensionRow, coherenceRow, certPkg⟩

theorem CompletionReflectionPacket_universal_real_seal_factorization [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              UnaryHistory sealRow ∧ UnaryHistory reflected ∧ UnaryHistory extension ∧
                Cont diagonal regular reflected ∧ Cont universal completion extension ∧
                  hsame reflected sealRow ∧ hsame extension package ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet reflectedRow reflectedSame extensionRow extensionSame
  obtain ⟨completionUnary, universalUnary, _separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    _packageRow, _provenanceRow, certPkg⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have sealUnary : UnaryHistory sealRow :=
    unary_transport reflectedUnary reflectedSame
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  exact
    ⟨sealUnary, reflectedUnary, extensionUnary, reflectedRow, extensionRow, reflectedSame,
      extensionSame, certPkg⟩

theorem CompletionReflectionPacket_standard_bridge_boundary [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg →
      Cont diagonal regular reflected →
        hsame reflected sealRow →
          Cont universal completion extension →
            hsame extension package →
              Cont reflected extension bridge →
                PkgSig bundle cert pkg →
                  UnaryHistory reflected ∧ UnaryHistory extension ∧ UnaryHistory bridge ∧
                    hsame reflected sealRow ∧ hsame extension package ∧
                      Cont diagonal regular reflected ∧ Cont universal completion extension ∧
                        Cont reflected extension bridge ∧ PkgSig bundle cert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet reflectedRow reflectedSame extensionRow extensionSame bridgeRow certPkg
  obtain ⟨completionUnary, universalUnary, _separatedUnary, diagonalUnary, regularUnary,
    _sealUnary, _transportUnary, _routeUnary, _packageUnary, _provenanceUnary, _certUnary,
    _packageRow, _provenanceRow, _packetCertPkg⟩ := packet
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed diagonalUnary regularUnary reflectedRow
  have extensionUnary : UnaryHistory extension :=
    unary_cont_closed universalUnary completionUnary extensionRow
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed reflectedUnary extensionUnary bridgeRow
  exact
    ⟨reflectedUnary, extensionUnary, bridgeUnary, reflectedSame, extensionSame,
      reflectedRow, extensionRow, bridgeRow, certPkg⟩

theorem CompletionReflectionPacket_regular_source_tail_reflection [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance cert
      reflected extension audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      Cont diagonal regular reflected ->
        hsame reflected sealRow ->
          Cont universal completion extension ->
            hsame extension package ->
              Cont route provenance audit ->
                PkgSig bundle audit pkg ->
                  UnaryHistory reflected ∧ UnaryHistory sealRow ∧ UnaryHistory extension ∧
                    UnaryHistory audit ∧ Cont diagonal regular reflected ∧
                      Cont universal completion extension ∧ Cont route provenance audit ∧
                        hsame reflected sealRow ∧ hsame extension package ∧
                          PkgSig bundle cert pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet reflectedRow reflectedSame extensionRow extensionSame auditRow auditPkg
  obtain ⟨_diagonalUnary, _regularUnary, reflectedUnary, sealUnary, extensionUnary,
    _routeUnary, _provenanceUnary, auditUnary, reflectedRoute, extensionRoute, auditRoute,
    reflectedSame', extensionSame', certPkg, auditPkg'⟩ :=
    CompletionReflectionPacket_stream_regseq_real_factor packet reflectedRow reflectedSame
      extensionRow extensionSame auditRow auditPkg
  exact
    ⟨reflectedUnary, sealUnary, extensionUnary, auditUnary, reflectedRoute, extensionRoute,
      auditRoute, reflectedSame', extensionSame', certPkg, auditPkg'⟩

theorem CompletionReflectionPacket_classifier_scope [AskSetup] [PackageSetup]
    {completion universal separated diagonal regular sealRow transport route package provenance
      cert completion' universal' separated' diagonal' regular' sealRow' transport' route'
      package' provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionReflectionPacket completion universal separated diagonal regular sealRow transport route
        package provenance cert bundle pkg ->
      hsame completion completion' ->
        hsame universal universal' ->
          hsame separated separated' ->
            hsame diagonal diagonal' ->
              hsame regular regular' ->
                hsame sealRow sealRow' ->
                  hsame transport transport' ->
                    hsame route route' ->
                      hsame cert cert' ->
                        Cont completion' universal' package' ->
                          Cont transport' route' provenance' ->
                            PkgSig bundle cert' pkg ->
                              CompletionReflectionPacket completion' universal' separated'
                                  diagonal' regular' sealRow' transport' route' package'
                                  provenance' cert' bundle pkg ∧
                                hsame package package' ∧ hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameCompletion sameUniversal sameSeparated sameDiagonal sameRegular sameSeal
    sameTransport sameRoute sameCert packageRow' provenanceRow' certPkg'
  obtain ⟨completionUnary, universalUnary, separatedUnary, diagonalUnary, regularUnary,
    sealUnary, transportUnary, routeUnary, packageUnary, provenanceUnary, certUnary,
    packageRow, provenanceRow, _certPkg⟩ := packet
  have completionUnary' : UnaryHistory completion' :=
    unary_transport completionUnary sameCompletion
  have universalUnary' : UnaryHistory universal' :=
    unary_transport universalUnary sameUniversal
  have separatedUnary' : UnaryHistory separated' :=
    unary_transport separatedUnary sameSeparated
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have regularUnary' : UnaryHistory regular' :=
    unary_transport regularUnary sameRegular
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary sameRoute
  have certUnary' : UnaryHistory cert' :=
    unary_transport certUnary sameCert
  have packageUnary' : UnaryHistory package' :=
    unary_cont_closed completionUnary' universalUnary' packageRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed transportUnary' routeUnary' provenanceRow'
  have samePackage : hsame package package' :=
    cont_respects_hsame sameCompletion sameUniversal packageRow packageRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoute provenanceRow provenanceRow'
  exact
    ⟨⟨completionUnary', universalUnary', separatedUnary', diagonalUnary', regularUnary',
        sealUnary', transportUnary', routeUnary', packageUnary', provenanceUnary', certUnary',
        packageRow', provenanceRow', certPkg'⟩,
      samePackage, sameProvenance⟩

end BEDC.Derived.CompletionReflectionUp
