import BEDC.Derived.RegularityModulusUp

namespace BEDC.Derived.RegularityModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularityModulusPacket_obligation_completeness [AskSetup] [PackageSetup]
    {precision modulus window transport ledger provenance nameRow consumer finalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularityModulusPacket precision modulus window transport ledger provenance nameRow
        bundle pkg ->
      Cont window provenance consumer ->
        Cont consumer nameRow finalRead ->
          PkgSig bundle consumer pkg ->
            PkgSig bundle finalRead pkg ->
              UnaryHistory precision ∧ UnaryHistory modulus ∧ UnaryHistory window ∧
                UnaryHistory transport ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
                  UnaryHistory consumer ∧ UnaryHistory finalRead ∧
                    Cont precision window transport ∧ Cont transport modulus ledger ∧
                      Cont ledger nameRow provenance ∧ Cont window provenance consumer ∧
                        Cont consumer nameRow finalRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumer pkg ∧ PkgSig bundle finalRead pkg := by
  intro packet consumerRow finalReadRow consumerPkg finalReadPkg
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
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed consumerUnary nameRowUnary finalReadRow
  exact
    ⟨precisionUnary, modulusUnary, windowUnary, transportUnary, ledgerUnary,
      provenanceUnary, consumerUnary, finalReadUnary, precisionWindowTransport,
      transportModulusLedger, ledgerNameProvenance, consumerRow, finalReadRow,
      provenancePkg, consumerPkg, finalReadPkg⟩

end BEDC.Derived.RegularityModulusUp
