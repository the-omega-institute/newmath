import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyLimitModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyLimitModulusPacket [AskSetup] [PackageSetup]
    (input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory modulus ∧ UnaryHistory precision ∧
    UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont input modulus threshold ∧
      Cont threshold precision window ∧ Cont window readback dyadicLedger ∧
        Cont dyadicLedger sealRow cert ∧ PkgSig bundle provenance pkg

theorem RegularCauchyLimitModulusPacket_diagonal_totality [AskSetup] [PackageSetup]
    {input modulus precision threshold window readback dyadicLedger sealRow provenance cert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyLimitModulusPacket input modulus precision threshold window readback
        dyadicLedger sealRow provenance cert bundle pkg ->
      UnaryHistory readback ->
        UnaryHistory threshold ∧ UnaryHistory window ∧ UnaryHistory dyadicLedger ∧
          UnaryHistory cert ∧ Cont input modulus threshold ∧ Cont threshold precision window ∧
            Cont window readback dyadicLedger ∧ Cont dyadicLedger sealRow cert ∧
              PkgSig bundle provenance pkg := by
  intro packet readbackUnary
  obtain ⟨inputUnary, modulusUnary, precisionUnary, sealRowUnary, _provenanceUnary,
    inputModulusThreshold, thresholdPrecisionWindow, windowReadbackDyadicLedger,
    dyadicLedgerSealRowCert, provenancePkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed inputUnary modulusUnary inputModulusThreshold
  have windowUnary : UnaryHistory window :=
    unary_cont_closed thresholdUnary precisionUnary thresholdPrecisionWindow
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadicLedger
  have certUnary : UnaryHistory cert :=
    unary_cont_closed dyadicLedgerUnary sealRowUnary dyadicLedgerSealRowCert
  exact
    ⟨thresholdUnary, windowUnary, dyadicLedgerUnary, certUnary, inputModulusThreshold,
      thresholdPrecisionWindow, windowReadbackDyadicLedger, dyadicLedgerSealRowCert,
      provenancePkg⟩

end BEDC.Derived.RegularCauchyLimitModulusUp
