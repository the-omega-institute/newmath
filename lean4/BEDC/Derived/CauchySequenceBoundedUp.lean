import BEDC.Derived.CauchySequenceBoundedUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CauchySequenceBoundedUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceBoundedCarrier_dyadic_bound_stability [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      transportedBound : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      hsame bound transportedBound ->
        PkgSig bundle transportedBound pkg ->
          UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory transportedBound ∧ hsame bound transportedBound ∧
              PkgSig bundle name pkg ∧ PkgSig bundle transportedBound pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame UnaryHistory PkgSig
  intro carrier boundSame transportedBoundPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, _routeUnary,
    _provenanceUnary, _scheduleModulusTolerance, _toleranceBoundReadback,
    _readbackRouteSeal, _provenanceTransportName, namePkg⟩ := carrier
  have transportedBoundUnary : UnaryHistory transportedBound :=
    unary_transport boundUnary boundSame
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, transportedBoundUnary, boundSame, namePkg,
      transportedBoundPkg⟩

theorem CauchySequenceBoundedCarrier_ledger_nonescape [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name
      ledgerRead escapedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            PkgSig bundle escapedRead pkg ->
              UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                UnaryHistory bound ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                  UnaryHistory provenance ∧ UnaryHistory ledgerRead ∧
                    UnaryHistory escapedRead ∧ Cont schedule modulus tolerance ∧
                      Cont tolerance bound readback ∧ Cont provenance transport name ∧
                        Cont bound transport ledgerRead ∧ Cont ledgerRead route escapedRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle escapedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, _readbackRouteSeal,
    provenanceTransportName, namePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, transportUnary, routeUnary,
      provenanceUnary, ledgerReadUnary, escapedReadUnary, scheduleModulusTolerance,
      toleranceBoundReadback, provenanceTransportName, boundTransportLedger, ledgerRouteEscaped,
      namePkg, escapedPkg⟩

theorem CauchySequenceBoundedCarrier_scoped_dependency_surface [AskSetup] [PackageSetup]
    {schedule modulus tolerance readback realSeal bound transport route provenance name ledgerRead
      escapedRead sealedConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceBoundedCarrier schedule modulus tolerance readback realSeal bound transport
        route provenance name bundle pkg ->
      UnaryHistory transport ->
        Cont bound transport ledgerRead ->
          Cont ledgerRead route escapedRead ->
            Cont escapedRead realSeal sealedConsumer ->
              PkgSig bundle sealedConsumer pkg ->
                UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                  UnaryHistory bound ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                    UnaryHistory provenance ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory escapedRead ∧ UnaryHistory sealedConsumer ∧
                        Cont schedule modulus tolerance ∧ Cont tolerance bound readback ∧
                          Cont readback route realSeal ∧ Cont provenance transport name ∧
                            Cont bound transport ledgerRead ∧
                              Cont ledgerRead route escapedRead ∧
                                Cont escapedRead realSeal sealedConsumer ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle sealedConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportUnary boundTransportLedger ledgerRouteEscaped escapedSealConsumer
    sealedConsumerPkg
  obtain ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, routeUnary,
    provenanceUnary, scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
    provenanceTransportName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary boundUnary toleranceBoundReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary routeUnary readbackRouteSeal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundUnary transportUnary boundTransportLedger
  have escapedReadUnary : UnaryHistory escapedRead :=
    unary_cont_closed ledgerReadUnary routeUnary ledgerRouteEscaped
  have sealedConsumerUnary : UnaryHistory sealedConsumer :=
    unary_cont_closed escapedReadUnary realSealUnary escapedSealConsumer
  exact
    ⟨scheduleUnary, modulusUnary, toleranceUnary, boundUnary, transportUnary, routeUnary,
      provenanceUnary, ledgerReadUnary, escapedReadUnary, sealedConsumerUnary,
      scheduleModulusTolerance, toleranceBoundReadback, readbackRouteSeal,
      provenanceTransportName, boundTransportLedger, ledgerRouteEscaped, escapedSealConsumer,
      namePkg, sealedConsumerPkg⟩

end BEDC.Derived.CauchySequenceBoundedUp
