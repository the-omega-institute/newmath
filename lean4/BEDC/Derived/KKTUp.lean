import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KKTPrimalDualReadbackPacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness comparison stationarityReadback
      ledgerReadback dependencyPkg namecertRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory feasibility ∧ UnaryHistory slackness ∧ UnaryHistory comparison ∧
      hsame stationarity (append primal residual) ∧ Cont primal residual stationarity ∧
        Cont stationarity feasibility stationarityReadback ∧
          Cont comparison slackness ledgerReadback ∧ PkgSig bundle dependencyPkg pkg ∧
            hsame namecertRow ledgerReadback

theorem KKTPrimalDualPacket_row_obligations [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison stationarityReadback
      ledgerReadback dependencyPkg namecertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualReadbackPacket primal dual residual stationarity feasibility slackness comparison
        stationarityReadback ledgerReadback dependencyPkg namecertRow bundle pkg ->
      UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
        UnaryHistory feasibility ∧ UnaryHistory slackness ∧ UnaryHistory comparison ∧
          UnaryHistory stationarity ∧ UnaryHistory stationarityReadback ∧
            UnaryHistory ledgerReadback ∧ hsame stationarity (append primal residual) ∧
              hsame ledgerReadback (append comparison slackness) ∧
                Cont primal residual stationarity ∧
                  Cont stationarity feasibility stationarityReadback ∧
                    Cont comparison slackness ledgerReadback ∧
                      PkgSig bundle dependencyPkg pkg ∧ hsame namecertRow ledgerReadback := by
  intro packet
  have primalUnary : UnaryHistory primal := packet.left
  have dualUnary : UnaryHistory dual := packet.right.left
  have residualUnary : UnaryHistory residual := packet.right.right.left
  have feasibilityUnary : UnaryHistory feasibility := packet.right.right.right.left
  have slacknessUnary : UnaryHistory slackness := packet.right.right.right.right.left
  have comparisonUnary : UnaryHistory comparison := packet.right.right.right.right.right.left
  have stationaritySame : hsame stationarity (append primal residual) :=
    packet.right.right.right.right.right.right.left
  have stationarityCont : Cont primal residual stationarity :=
    packet.right.right.right.right.right.right.right.left
  have stationarityReadbackCont : Cont stationarity feasibility stationarityReadback :=
    packet.right.right.right.right.right.right.right.right.left
  have ledgerReadbackCont : Cont comparison slackness ledgerReadback :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle dependencyPkg pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have namecertSame : hsame namecertRow ledgerReadback :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  have stationarityUnary : UnaryHistory stationarity :=
    unary_cont_closed primalUnary residualUnary stationarityCont
  have stationarityReadbackUnary : UnaryHistory stationarityReadback :=
    unary_cont_closed stationarityUnary feasibilityUnary stationarityReadbackCont
  have ledgerReadbackUnary : UnaryHistory ledgerReadback :=
    unary_cont_closed comparisonUnary slacknessUnary ledgerReadbackCont
  exact
    ⟨primalUnary, dualUnary, residualUnary, feasibilityUnary, slacknessUnary,
      comparisonUnary, stationarityUnary, stationarityReadbackUnary, ledgerReadbackUnary,
      stationaritySame, ledgerReadbackCont, stationarityCont, stationarityReadbackCont,
      ledgerReadbackCont, pkgSig, namecertSame⟩

def KKTPrimalDualCarrier [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasible slack ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory stationarity ∧ UnaryHistory feasible ∧ UnaryHistory slack ∧
      UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont primal residual stationarity ∧
        Cont dual slack ledger ∧ Cont stationarity feasible provenance ∧
          PkgSig bundle provenance pkg

theorem KKTPrimalDualCarrier_primal_dual_row_obligations [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasible slack ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger provenance
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          hsame ∧
        UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
          UnaryHistory stationarity ∧ UnaryHistory feasible ∧ UnaryHistory slack ∧
            UnaryHistory ledger ∧ UnaryHistory provenance ∧
              Cont primal residual stationarity ∧ Cont dual slack ledger ∧
                Cont stationarity feasible provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert carrier

theorem KKTPrimalDualCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasible slack ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger provenance
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          hsame := by
  intro carrier
  exact (KKTPrimalDualCarrier_primal_dual_row_obligations carrier).left

def KKTComplementarityLedger [AskSetup] [PackageSetup]
    (residual multiplier slack ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory residual ∧ UnaryHistory multiplier ∧ UnaryHistory slack ∧
    UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont residual multiplier ledger ∧
      Cont ledger slack endpoint ∧ PkgSig bundle endpoint pkg

theorem KKTComplementarityLedger_exactness [AskSetup] [PackageSetup]
    {residual multiplier slack ledger endpoint residual' multiplier' slack' ledger'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTComplementarityLedger residual multiplier slack ledger endpoint bundle pkg ->
      hsame residual residual' -> hsame multiplier multiplier' -> hsame slack slack' ->
        Cont residual' multiplier' ledger' -> Cont ledger' slack' endpoint' ->
          PkgSig bundle endpoint' pkg ->
            KKTComplementarityLedger residual' multiplier' slack' ledger' endpoint' bundle pkg ∧
              hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameResidual sameMultiplier sameSlack residualLedger' endpointLedger' pkgSig'
  have residualUnary' : UnaryHistory residual' :=
    unary_transport packet.left sameResidual
  have multiplierUnary' : UnaryHistory multiplier' :=
    unary_transport packet.right.left sameMultiplier
  have slackUnary' : UnaryHistory slack' :=
    unary_transport packet.right.right.left sameSlack
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResidual sameMultiplier packet.right.right.right.right.right.left
      residualLedger'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed residualUnary' multiplierUnary' residualLedger'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameSlack packet.right.right.right.right.right.right.left
      endpointLedger'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary' slackUnary' endpointLedger'
  exact
    And.intro
      (And.intro residualUnary'
        (And.intro multiplierUnary'
          (And.intro slackUnary'
            (And.intro ledgerUnary'
              (And.intro endpointUnary'
                (And.intro residualLedger'
                  (And.intro endpointLedger' pkgSig')))))))
      (And.intro sameLedger sameEndpoint)

def KKTPrimalDualPacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory stationarity ∧ UnaryHistory feasibility ∧ UnaryHistory slackness ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont primal dual residual ∧
        Cont residual stationarity feasibility ∧ Cont feasibility slackness endpoint ∧
          PkgSig probe provenance pkg

theorem KKTPrimalDualPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualPacket primal dual residual stationarity feasibility slackness provenance
        endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          hsame ∧
        Cont primal dual residual ∧ Cont residual stationarity feasibility ∧
          Cont feasibility slackness endpoint ∧ PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
            provenance e probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KKTPrimalDualPacket primal dual residual stationarity feasibility slackness
                provenance e probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right.right)))

theorem KKTPrimalDualPacket_stationarity_feasibility_hsame_transport [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness provenance endpoint primalNext
      dualNext residualNext stationarityNext feasibilityNext slacknessNext provenanceNext
      endpointNext : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualPacket primal dual residual stationarity feasibility slackness provenance endpoint
        probe pkg ->
      hsame primal primalNext ->
        hsame dual dualNext ->
          hsame residual residualNext ->
            hsame stationarity stationarityNext ->
              hsame feasibility feasibilityNext ->
                hsame slackness slacknessNext ->
                  hsame provenance provenanceNext ->
                    hsame endpoint endpointNext ->
                      PkgSig probe provenanceNext pkg ->
                        KKTPrimalDualPacket primalNext dualNext residualNext stationarityNext
                            feasibilityNext slacknessNext provenanceNext endpointNext probe pkg ∧
                          hsame endpoint endpointNext := by
  intro packet samePrimal sameDual sameResidual sameStationarity sameFeasibility sameSlackness
    sameProvenance sameEndpoint pkgSig
  have primalUnary : UnaryHistory primalNext :=
    unary_transport packet.left samePrimal
  have dualUnary : UnaryHistory dualNext :=
    unary_transport packet.right.left sameDual
  have residualUnary : UnaryHistory residualNext :=
    unary_transport packet.right.right.left sameResidual
  have stationarityUnary : UnaryHistory stationarityNext :=
    unary_transport packet.right.right.right.left sameStationarity
  have feasibilityUnary : UnaryHistory feasibilityNext :=
    unary_transport packet.right.right.right.right.left sameFeasibility
  have slacknessUnary : UnaryHistory slacknessNext :=
    unary_transport packet.right.right.right.right.right.left sameSlackness
  have provenanceUnary : UnaryHistory provenanceNext :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have endpointUnary : UnaryHistory endpointNext :=
    unary_transport packet.right.right.right.right.right.right.right.left sameEndpoint
  have residualRow : Cont primalNext dualNext residualNext :=
    cont_hsame_transport samePrimal sameDual sameResidual
      packet.right.right.right.right.right.right.right.right.left
  have feasibilityRow : Cont residualNext stationarityNext feasibilityNext :=
    cont_hsame_transport sameResidual sameStationarity sameFeasibility
      packet.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont feasibilityNext slacknessNext endpointNext :=
    cont_hsame_transport sameFeasibility sameSlackness sameEndpoint
      packet.right.right.right.right.right.right.right.right.right.right.left
  exact And.intro
    (And.intro primalUnary
      (And.intro dualUnary
        (And.intro residualUnary
          (And.intro stationarityUnary
            (And.intro feasibilityUnary
              (And.intro slacknessUnary
                (And.intro provenanceUnary
                  (And.intro endpointUnary
                    (And.intro residualRow
                      (And.intro feasibilityRow
                        (And.intro endpointRow pkgSig)))))))))))
    sameEndpoint

def KKTCarrierPacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness comparison ledger provenance
      endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory feasibility ∧ Cont primal dual comparison ∧
      Cont residual stationarity slackness ∧ Cont feasibility slackness ledger ∧
        Cont ledger provenance endpoint ∧ PkgSig probe endpoint pkg

theorem KKTCarrierPacket_endpoint_obligation [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison ledger provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison ledger
        provenance endpoint probe pkg ->
      UnaryHistory comparison ∧ Cont residual stationarity slackness ∧
        Cont feasibility slackness ledger ∧ Cont ledger provenance endpoint ∧
          hsame comparison (append primal dual) ∧
            hsame slackness (append residual stationarity) ∧
              hsame ledger (append feasibility slackness) ∧
                hsame endpoint (append ledger provenance) ∧ PkgSig probe endpoint pkg := by
  intro packet
  cases packet with
  | intro primalUnary rest =>
      cases rest with
      | intro dualUnary rest =>
          cases rest with
          | intro _residualUnary rest =>
              cases rest with
              | intro _feasibilityUnary rest =>
                  cases rest with
                  | intro comparisonCont rest =>
                      cases rest with
                      | intro slacknessCont rest =>
                          cases rest with
                          | intro ledgerCont rest =>
                              cases rest with
                              | intro endpointCont endpointPkg =>
                                  have comparisonUnary : UnaryHistory comparison :=
                                    unary_cont_closed primalUnary dualUnary comparisonCont
                                  exact And.intro comparisonUnary
                                    (And.intro slacknessCont
                                      (And.intro ledgerCont
                                        (And.intro endpointCont
                                          (And.intro comparisonCont
                                            (And.intro slacknessCont
                                              (And.intro ledgerCont
                                                (And.intro endpointCont endpointPkg)))))))

theorem KKTCarrierPacket_downstream_consumer_boundary [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison ledger provenance
      endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison ledger
        provenance endpoint probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame ∧
        Cont primal dual comparison ∧ Cont residual stationarity slackness ∧
          Cont feasibility slackness ledger ∧ Cont ledger provenance endpoint ∧
            hsame comparison (append primal dual) ∧
              hsame slackness (append residual stationarity) ∧
                hsame ledger (append feasibility slackness) ∧
                  hsame endpoint (append ledger provenance) ∧ PkgSig probe endpoint pkg := by
  intro packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison
              ledger provenance endpoint probe pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  have rows :=
    KKTCarrierPacket_endpoint_obligation packet
  exact And.intro cert
    (And.intro packet.right.right.right.right.left
      (And.intro rows.right.left
        (And.intro rows.right.right.left
          (And.intro rows.right.right.right.left
            (And.intro rows.right.right.right.right.left
              (And.intro rows.right.right.right.right.right.left
                (And.intro rows.right.right.right.right.right.right.left
                  (And.intro rows.right.right.right.right.right.right.right.left
                    rows.right.right.right.right.right.right.right.right))))))))

theorem KKTCarrierPacket_stationarity_feasibility_stability [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison ledger provenance
      endpoint primal' dual' residual' stationarity' feasibility' slackness' comparison'
      ledger' provenance' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison ledger
        provenance endpoint probe pkg ->
      hsame primal primal' ->
        hsame dual dual' ->
          hsame residual residual' ->
            hsame stationarity stationarity' ->
              hsame feasibility feasibility' ->
                hsame provenance provenance' ->
                  Cont primal' dual' comparison' ->
                    Cont residual' stationarity' slackness' ->
                      Cont feasibility' slackness' ledger' ->
                        Cont ledger' provenance' endpoint' ->
                          PkgSig probe endpoint' pkg ->
                            KKTCarrierPacket primal' dual' residual' stationarity'
                                feasibility' slackness' comparison' ledger' provenance'
                                endpoint' probe pkg ∧
                              hsame comparison comparison' ∧ hsame slackness slackness' ∧
                                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet samePrimal sameDual sameResidual sameStationarity sameFeasibility
    sameProvenance primalDualComparison residualStationaritySlackness
    feasibilitySlacknessLedger ledgerProvenanceEndpoint endpointPkg
  rcases packet with
    ⟨primalUnary, dualUnary, residualUnary, feasibilityUnary, primalDualComparisonOld,
      residualStationaritySlacknessOld, feasibilitySlacknessLedgerOld,
      ledgerProvenanceEndpointOld, _endpointPkgOld⟩
  have primalUnary' : UnaryHistory primal' :=
    unary_transport primalUnary samePrimal
  have dualUnary' : UnaryHistory dual' :=
    unary_transport dualUnary sameDual
  have residualUnary' : UnaryHistory residual' :=
    unary_transport residualUnary sameResidual
  have feasibilityUnary' : UnaryHistory feasibility' :=
    unary_transport feasibilityUnary sameFeasibility
  have sameComparison : hsame comparison comparison' :=
    cont_respects_hsame samePrimal sameDual primalDualComparisonOld primalDualComparison
  have sameSlackness : hsame slackness slackness' :=
    cont_respects_hsame sameResidual sameStationarity residualStationaritySlacknessOld
      residualStationaritySlackness
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameFeasibility sameSlackness feasibilitySlacknessLedgerOld
      feasibilitySlacknessLedger
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameProvenance ledgerProvenanceEndpointOld
      ledgerProvenanceEndpoint
  exact
    ⟨⟨primalUnary', dualUnary', residualUnary', feasibilityUnary', primalDualComparison,
        residualStationaritySlackness, feasibilitySlacknessLedger, ledgerProvenanceEndpoint,
        endpointPkg⟩,
      sameComparison, sameSlackness, sameLedger, sameEndpoint⟩

theorem KKTCarrierPacket_stationarity_feasibility_hsame_transport [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison ledger provenance endpoint
      primal' dual' residual' stationarity' feasibility' slackness' comparison' ledger'
      provenance' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTCarrierPacket primal dual residual stationarity feasibility slackness comparison ledger
        provenance endpoint probe pkg ->
      hsame primal primal' ->
        hsame dual dual' ->
          hsame residual residual' ->
            hsame stationarity stationarity' ->
              hsame feasibility feasibility' ->
                hsame provenance provenance' ->
                  Cont primal' dual' comparison' ->
                    Cont residual' stationarity' slackness' ->
                      Cont feasibility' slackness' ledger' ->
                        Cont ledger' provenance' endpoint' ->
                          PkgSig probe endpoint' pkg ->
                            KKTCarrierPacket primal' dual' residual' stationarity' feasibility'
                                slackness' comparison' ledger' provenance' endpoint' probe pkg ∧
                              hsame comparison comparison' ∧
                                hsame slackness slackness' ∧ hsame ledger ledger' ∧
                                  hsame endpoint endpoint' := by
  exact KKTCarrierPacket_stationarity_feasibility_stability

end BEDC.Derived.KKTUp
