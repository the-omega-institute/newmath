import BEDC.Derived.DyadicTailBoundUp

namespace BEDC.Derived.DyadicTailBoundUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicTailBoundCarrier_zero_packet_carrier [AskSetup] [PackageSetup]
    {precision schedule tolerance ledger readback sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory precision ->
      UnaryHistory schedule ->
        UnaryHistory tolerance ->
          UnaryHistory readback ->
            UnaryHistory provenance ->
              UnaryHistory localCert ->
                Cont schedule tolerance ledger ->
                  Cont ledger readback sealRow ->
                    Cont precision sealRow transport ->
                      Cont transport localCert route ->
                        Cont route provenance sealRow ->
                          PkgSig bundle provenance pkg ->
                            DyadicTailBoundCarrier precision schedule tolerance ledger readback
                                sealRow transport route provenance localCert bundle pkg ∧
                              UnaryHistory ledger ∧ UnaryHistory sealRow ∧
                                UnaryHistory transport ∧ UnaryHistory route := by
  intro precisionUnary scheduleUnary toleranceUnary readbackUnary provenanceUnary localCertUnary
    scheduleToleranceLedger ledgerReadbackSeal precisionSealTransport transportLocalRoute
    routeProvenanceSeal provenancePkg
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary toleranceUnary scheduleToleranceLedger
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed ledgerUnary readbackUnary ledgerReadbackSeal
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed precisionUnary sealUnary precisionSealTransport
  have routeUnary : UnaryHistory route :=
    unary_cont_closed transportUnary localCertUnary transportLocalRoute
  have carrier :
      DyadicTailBoundCarrier precision schedule tolerance ledger readback sealRow transport route
          provenance localCert bundle pkg :=
    ⟨precisionUnary,
      scheduleUnary,
      toleranceUnary,
      readbackUnary,
      sealUnary,
      provenanceUnary,
      scheduleToleranceLedger,
      ledgerReadbackSeal,
      precisionSealTransport,
      transportLocalRoute,
      routeProvenanceSeal,
      provenancePkg⟩
  exact ⟨carrier, ledgerUnary, sealUnary, transportUnary, routeUnary⟩

end BEDC.Derived.DyadicTailBoundUp
