import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularityModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularityModulusPacket [AskSetup] [PackageSetup]
    (precision modulus window transport ledger provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
    UnaryHistory nameRow ∧ Cont precision window transport ∧ Cont transport modulus ledger ∧
      Cont ledger nameRow provenance ∧ PkgSig bundle provenance pkg

theorem RegularityModulusPacket_window_monotonicity [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow precision' modulus' window'
      transport' ledger' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      hsame precision precision' -> hsame modulus modulus' -> hsame window window' ->
        hsame nameRow nameRow' -> Cont precision' window' transport' ->
          Cont transport' modulus' ledger' -> Cont ledger' nameRow' provenance' ->
            PkgSig bundle provenance' pkg ->
              RegularityModulusPacket precision' modulus' window' transport' ledger'
                  provenance' nameRow' bundle pkg ∧
                hsame transport transport' ∧ hsame ledger ledger' ∧
                  hsame provenance provenance' := by
  intro packet samePrecision sameModulus sameWindow sameNameRow transportRow' ledgerRow'
    provenanceRow' pkgSig'
  have transportRow : Cont precision window transport :=
    packet.right.right.right.right.left
  have ledgerRow : Cont transport modulus ledger :=
    packet.right.right.right.right.right.left
  have provenanceRow : Cont ledger nameRow provenance :=
    packet.right.right.right.right.right.right.left
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameWindow transportRow transportRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTransport sameModulus ledgerRow ledgerRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameNameRow provenanceRow provenanceRow'
  have transported :
      RegularityModulusPacket precision' modulus' window' transport' ledger' provenance'
          nameRow' bundle pkg :=
    ⟨unary_transport packet.left samePrecision,
      unary_transport packet.right.left sameModulus,
      unary_transport packet.right.right.left sameWindow,
      unary_transport packet.right.right.right.left sameNameRow,
      transportRow',
      ledgerRow',
      provenanceRow',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameTransport
      (And.intro sameLedger sameProvenance))

theorem RegularityModulusDyadicWindowCarrier_window_monotonicity [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow precision' modulus' window'
      transport' ledger' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      hsame precision precision' -> hsame modulus modulus' -> hsame window window' ->
        hsame nameRow nameRow' -> Cont precision' window' transport' ->
          Cont transport' modulus' ledger' -> Cont ledger' nameRow' provenance' ->
            PkgSig bundle provenance' pkg ->
              RegularityModulusPacket precision' modulus' window' transport' ledger'
                  provenance' nameRow' bundle pkg ∧
                hsame transport transport' ∧ hsame ledger ledger' ∧
                  hsame provenance provenance' :=
    RegularityModulusPacket_window_monotonicity

theorem RegularityModulusPacket_common_window_exactness [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow precision' modulus' window'
      transport' ledger' provenance' nameRow' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      RegularityModulusPacket precision' modulus' window' transport' ledger' provenance'
        nameRow' bundle' pkg' ->
        hsame precision precision' ->
          hsame modulus modulus' ->
            hsame window window' ->
              hsame nameRow nameRow' ->
                hsame transport transport' ∧ hsame ledger ledger' ∧
                  hsame provenance provenance' := by
  intro packet packet' samePrecision sameModulus sameWindow sameNameRow
  have transportRow : Cont precision window transport :=
    packet.right.right.right.right.left
  have transportRow' : Cont precision' window' transport' :=
    packet'.right.right.right.right.left
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameWindow transportRow transportRow'
  have ledgerRow : Cont transport modulus ledger :=
    packet.right.right.right.right.right.left
  have ledgerRow' : Cont transport' modulus' ledger' :=
    packet'.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTransport sameModulus ledgerRow ledgerRow'
  have provenanceRow : Cont ledger nameRow provenance :=
    packet.right.right.right.right.right.right.left
  have provenanceRow' : Cont ledger' nameRow' provenance' :=
    packet'.right.right.right.right.right.right.left
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameNameRow provenanceRow provenanceRow'
  exact And.intro sameTransport (And.intro sameLedger sameProvenance)

theorem RegularityModulusPacket_regseqrat_consumption_boundary [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      Cont window provenance consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
            UnaryHistory provenance ∧ UnaryHistory consumer ∧
              Cont precision window transport ∧ Cont ledger nameRow provenance ∧
                Cont window provenance consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg := by
  intro packet consumerRow consumerPkg
  obtain ⟨precisionUnary, modulusUnary, windowUnary, nameRowUnary, transportRow, ledgerRow,
    provenanceRow, provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed precisionUnary windowUnary transportRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed transportUnary modulusUnary ledgerRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary nameRowUnary provenanceRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary consumerRow
  exact
    ⟨precisionUnary, modulusUnary, windowUnary, provenanceUnary, consumerUnary, transportRow,
      provenanceRow, consumerRow, provenancePkg, consumerPkg⟩

theorem RegularityModulusPacket_dyadic_window_exactness [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      Cont ledger (BHist.e1 nameRow) provenance -> False := by
  intro packet extendedNameRoute
  have provenanceRow : Cont ledger nameRow provenance :=
    packet.right.right.right.right.right.right.left
  have sameName : hsame nameRow (BHist.e1 nameRow) :=
    cont_left_cancel provenanceRow extendedNameRoute
  exact hsame_extension_self_absurd.right nameRow (hsame_symm sameName)

theorem RegularityModulusPacket_realup_seal_handoff [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      Cont provenance nameRow sealRow ->
        PkgSig bundle sealRow pkg ->
          UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
            UnaryHistory ledger ∧ UnaryHistory provenance ∧ UnaryHistory sealRow ∧
              Cont precision window transport ∧ Cont transport modulus ledger ∧
                Cont ledger nameRow provenance ∧ Cont provenance nameRow sealRow ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealRow pkg := by
  intro packet sealRowCont sealRowPkg
  obtain ⟨precisionUnary, modulusUnary, windowUnary, nameRowUnary, precisionWindowTransport,
    transportModulusLedger, ledgerNameProvenance, provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed precisionUnary windowUnary precisionWindowTransport
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed transportUnary modulusUnary transportModulusLedger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameProvenance
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed provenanceUnary nameRowUnary sealRowCont
  exact
    ⟨precisionUnary, modulusUnary, windowUnary, ledgerUnary, provenanceUnary, sealRowUnary,
      precisionWindowTransport, transportModulusLedger, ledgerNameProvenance, sealRowCont,
      provenancePkg, sealRowPkg⟩

theorem RegularityModulusPacket_shared_rate_consumer_exhaustion [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      Cont window provenance consumer ->
        Cont consumer nameRow consumer' ->
          PkgSig bundle consumer' pkg ->
            UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
              UnaryHistory transport ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
                UnaryHistory consumer ∧ UnaryHistory consumer' ∧
                  Cont precision window transport ∧ Cont transport modulus ledger ∧
                    Cont ledger nameRow provenance ∧ Cont window provenance consumer ∧
                      Cont consumer nameRow consumer' ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle consumer' pkg := by
  intro packet consumerRow consumerNameRow consumerPkg
  obtain ⟨precisionUnary, modulusUnary, windowUnary, nameRowUnary, precisionWindowTransport,
    transportModulusLedger, ledgerNameProvenance, provenancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed precisionUnary windowUnary precisionWindowTransport
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed transportUnary modulusUnary transportModulusLedger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameProvenance
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary provenanceUnary consumerRow
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed consumerUnary nameRowUnary consumerNameRow
  exact
    ⟨precisionUnary, modulusUnary, windowUnary, transportUnary, ledgerUnary, provenanceUnary,
      consumerUnary, consumerUnary', precisionWindowTransport, transportModulusLedger,
      ledgerNameProvenance, consumerRow, consumerNameRow, provenancePkg, consumerPkg⟩

end BEDC.Derived.RegularityModulusUp
