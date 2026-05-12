import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ComputableRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ComputableRealSourcePacket [AskSetup] [PackageSetup]
    (stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
    UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
      Cont transport routes provenance ∧ Cont provenance name endpoint ∧
        PkgSig bundle endpoint pkg

theorem ComputableRealSourcePacket_ledger_coverage [AskSetup] [PackageSetup]
    {stream modulus dyadic regseq «seal» transport routes provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealSourcePacket stream modulus dyadic regseq «seal» transport routes provenance
        name endpoint bundle pkg ->
      UnaryHistory stream ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
        UnaryHistory «seal» ∧ Cont stream modulus transport ∧ Cont dyadic regseq routes ∧
          Cont transport routes provenance ∧ Cont provenance name endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact packet.left
  · constructor
    · exact packet.right.left
    · constructor
      · exact packet.right.right.left
      · constructor
        · exact packet.right.right.right.left
        · constructor
          · exact packet.right.right.right.right.left
          · constructor
            · exact packet.right.right.right.right.right.left
            · constructor
              · exact packet.right.right.right.right.right.right.left
              · constructor
                · exact packet.right.right.right.right.right.right.right.left
                · constructor
                  · exact packet.right.right.right.right.right.right.right.right.left
                  · exact packet.right.right.right.right.right.right.right.right.right

def ComputableRealPacket [AskSetup] [PackageSetup]
    (schedule modulus dyadic regular sealRow transport approximationLedger sealLedger provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory sealRow ∧ UnaryHistory nameRow ∧
      Cont schedule modulus transport ∧ Cont dyadic regular approximationLedger ∧
        Cont transport approximationLedger sealLedger ∧ Cont sealLedger nameRow provenance ∧
          PkgSig bundle provenance pkg

theorem ComputableRealPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {schedule modulus dyadic regular sealRow transport approximationLedger sealLedger provenance
      nameRow schedule' modulus' dyadic' regular' sealRow' transport' approximationLedger'
      sealLedger' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ComputableRealPacket schedule modulus dyadic regular sealRow transport approximationLedger
        sealLedger provenance nameRow bundle pkg ->
      hsame schedule schedule' ->
        hsame modulus modulus' ->
          hsame dyadic dyadic' ->
            hsame regular regular' ->
              hsame sealRow sealRow' ->
                hsame nameRow nameRow' ->
                  Cont schedule' modulus' transport' ->
                    Cont dyadic' regular' approximationLedger' ->
                      Cont transport' approximationLedger' sealLedger' ->
                        Cont sealLedger' nameRow' provenance' ->
                          PkgSig bundle provenance' pkg ->
                            ComputableRealPacket schedule' modulus' dyadic' regular' sealRow'
                                transport' approximationLedger' sealLedger' provenance' nameRow'
                                bundle pkg ∧
                              UnaryHistory dyadic' ∧ UnaryHistory regular' ∧
                                UnaryHistory sealRow' ∧ hsame transport transport' ∧
                                  hsame approximationLedger approximationLedger' ∧
                                    hsame sealLedger sealLedger' := by
  intro packet sameSchedule sameModulus sameDyadic sameRegular sameSeal sameNameRow
    transportRow approximationRow sealLedgerRow provenanceRow provenancePkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, regularUnary, sealUnary, nameRowUnary,
    transportOld, approximationOld, sealLedgerOld, _provenanceOld, _pkgOld⟩ := packet
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have regularUnary' : UnaryHistory regular' :=
    unary_transport regularUnary sameRegular
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameSchedule sameModulus transportOld transportRow
  have sameApproximation : hsame approximationLedger approximationLedger' :=
    cont_respects_hsame sameDyadic sameRegular approximationOld approximationRow
  have sameSealLedger : hsame sealLedger sealLedger' :=
    cont_respects_hsame sameTransport sameApproximation sealLedgerOld sealLedgerRow
  exact
    ⟨⟨scheduleUnary', modulusUnary', dyadicUnary', regularUnary', sealUnary', nameRowUnary',
        transportRow, approximationRow, sealLedgerRow, provenanceRow, provenancePkg⟩,
      dyadicUnary', regularUnary', sealUnary', sameTransport, sameApproximation,
      sameSealLedger⟩

end BEDC.Derived.ComputableRealUp
