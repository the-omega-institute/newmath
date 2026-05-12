import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealDiagonalCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealDiagonalCompletionSourcePacket [AskSetup] [PackageSetup]
    (inputFamily modulus selector schedule readback «seal» provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory inputFamily ∧ UnaryHistory modulus ∧ UnaryHistory schedule ∧
    UnaryHistory «seal» ∧ UnaryHistory provenance ∧ Cont inputFamily modulus selector ∧
      Cont selector schedule readback ∧ Cont readback «seal» localCert ∧
        Cont localCert provenance «seal» ∧ PkgSig bundle provenance pkg

theorem RealDiagonalCompletionSourcePacket_carrier_habitation [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback «seal» provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory inputFamily ->
      UnaryHistory modulus ->
        UnaryHistory schedule ->
          UnaryHistory «seal» ->
            UnaryHistory provenance ->
              Cont inputFamily modulus selector ->
                Cont selector schedule readback ->
                  Cont readback «seal» localCert ->
                    Cont localCert provenance «seal» ->
                      PkgSig bundle provenance pkg ->
                        RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule
                            readback «seal» provenance localCert bundle pkg ∧
                          UnaryHistory selector ∧ UnaryHistory readback ∧
                            UnaryHistory localCert := by
  intro inputUnary modulusUnary scheduleUnary sealUnary provenanceUnary selectorRow
    readbackRow localCertRow sealRow provenanceSig
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary selectorRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary readbackRow
  have localCertUnary : UnaryHistory localCert :=
    unary_cont_closed readbackUnary sealUnary localCertRow
  exact
    ⟨⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, provenanceUnary, selectorRow,
        readbackRow, localCertRow, sealRow, provenanceSig⟩,
      selectorUnary, readbackUnary, localCertUnary⟩

theorem RealDiagonalCompletionSourcePacket_ledger_exactness [AskSetup] [PackageSetup]
    {inputFamily modulus selector schedule readback «seal» provenance localCert consumerRead
      diagonalRead rationalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDiagonalCompletionSourcePacket inputFamily modulus selector schedule readback «seal»
        provenance localCert bundle pkg ->
      Cont selector schedule diagonalRead ->
        Cont diagonalRead readback rationalRead ->
          Cont rationalRead «seal» consumerRead ->
            UnaryHistory selector ∧ UnaryHistory schedule ∧ UnaryHistory readback ∧
              UnaryHistory «seal» ∧ UnaryHistory diagonalRead ∧ UnaryHistory rationalRead ∧
                UnaryHistory consumerRead ∧ Cont selector schedule diagonalRead ∧
                  Cont diagonalRead readback rationalRead ∧
                    Cont rationalRead «seal» consumerRead ∧ PkgSig bundle provenance pkg := by
  intro packet diagonalRow rationalRow consumerRow
  obtain ⟨inputUnary, modulusUnary, scheduleUnary, sealUnary, _provenanceUnary,
    _selectorRow, _readbackRow, _localCertRow, _sealRow, pkgSig⟩ := packet
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed inputUnary modulusUnary _selectorRow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectorUnary scheduleUnary _readbackRow
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectorUnary scheduleUnary diagonalRow
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed diagonalUnary readbackUnary rationalRow
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rationalUnary sealUnary consumerRow
  exact
    ⟨selectorUnary, scheduleUnary, readbackUnary, sealUnary, diagonalUnary,
      rationalUnary, consumerUnary, diagonalRow, rationalRow, consumerRow, pkgSig⟩

end BEDC.Derived.RealDiagonalCompletionUp
