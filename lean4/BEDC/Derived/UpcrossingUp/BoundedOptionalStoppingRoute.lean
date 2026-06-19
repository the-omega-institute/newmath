import BEDC.Derived.UpcrossingUp.FiniteLedgerHandoff

namespace BEDC.Derived.UpcrossingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpcrossingBoundedOptionalStoppingRoute [AskSetup] [PackageSetup]
    {source martingale window threshold route provenance localCert lowerHit upperHit completed
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UpcrossingCarrier source martingale window threshold route provenance localCert bundle pkg →
      Cont window threshold lowerHit →
        Cont lowerHit threshold upperHit →
          Cont lowerHit upperHit completed →
            Cont completed route handoff →
              PkgSig bundle completed pkg →
                PkgSig bundle handoff pkg →
                  UnaryHistory lowerHit ∧ UnaryHistory upperHit ∧ UnaryHistory completed ∧
                    UnaryHistory handoff ∧ Cont window threshold lowerHit ∧
                      Cont lowerHit threshold upperHit ∧ Cont lowerHit upperHit completed ∧
                        Cont completed route handoff ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle completed pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lowerCont upperCont completedCont handoffCont completedPkg handoffPkg
  obtain ⟨lowerUnary, upperUnary, completedUnary, handoffUnary, lowerContProof,
    upperContProof, completedContProof, handoffContProof, provenancePkg, handoffPkgProof⟩ :=
      UpcrossingFiniteLedgerHandoff carrier lowerCont upperCont completedCont handoffCont handoffPkg
  exact
    ⟨lowerUnary, upperUnary, completedUnary, handoffUnary, lowerContProof, upperContProof,
      completedContProof, handoffContProof, provenancePkg, completedPkg, handoffPkgProof⟩

end BEDC.Derived.UpcrossingUp
