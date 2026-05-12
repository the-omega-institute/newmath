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

end BEDC.Derived.RealDiagonalCompletionUp
