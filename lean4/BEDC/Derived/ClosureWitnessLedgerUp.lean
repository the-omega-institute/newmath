import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosureWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosureWitnessLedgerCarrier [AskSetup] [PackageSetup]
    (generator provenance witness classifier gap transports routes pkgRow certRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generator ∧ UnaryHistory provenance ∧ UnaryHistory witness ∧
    UnaryHistory gap ∧ UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory certRow ∧
      Cont generator provenance witness ∧ Cont witness gap classifier ∧
        Cont classifier routes pkgRow ∧ Cont pkgRow certRow transports ∧
          PkgSig bundle pkgRow pkg

theorem ClosureWitnessLedgerCarrier_classifier_stability [AskSetup] [PackageSetup]
    {generator provenance witness classifier gap transports routes pkgRow certRow generator'
      provenance' witness' gap' classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosureWitnessLedgerCarrier generator provenance witness classifier gap transports routes
        pkgRow certRow bundle pkg →
      hsame generator generator' →
        hsame provenance provenance' →
          hsame witness witness' →
            hsame gap gap' →
              Cont witness' gap' classifier' →
                ClosureWitnessLedgerCarrier generator' provenance' witness' classifier' gap'
                    transports routes pkgRow certRow bundle pkg ∧ hsame classifier classifier' := by
  intro carrier sameGenerator sameProvenance sameWitness sameGap classifierRow'
  cases sameGenerator
  cases sameProvenance
  cases sameWitness
  cases sameGap
  obtain ⟨generatorUnary, provenanceUnary, witnessUnary, gapUnary, transportsUnary, routesUnary,
    certUnary, generatorWitnessRow, classifierRow, classifierPkgRow, pkgCertTransportRow,
    pkgSig⟩ := carrier
  have classifierSame : hsame classifier classifier' :=
    cont_respects_hsame (hsame_refl witness) (hsame_refl gap) classifierRow classifierRow'
  have classifierPkgRow' : Cont classifier' routes pkgRow := by
    cases classifierSame
    exact classifierPkgRow
  exact And.intro
    ⟨generatorUnary, provenanceUnary, witnessUnary, gapUnary, transportsUnary, routesUnary,
      certUnary, generatorWitnessRow, classifierRow', classifierPkgRow', pkgCertTransportRow,
      pkgSig⟩
    classifierSame

end BEDC.Derived.ClosureWitnessLedgerUp
