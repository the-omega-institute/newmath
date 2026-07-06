import BEDC.Derived.TheorySelfClassifierUp.TasteGate

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_carrier_obligation [AskSetup] [PackageSetup]
    {G E R P A L H C Q N read : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg ->
      Cont L N read ->
        PkgSig bundle read pkg ->
          UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧
            UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory Q ∧ UnaryHistory N ∧ UnaryHistory read ∧ Cont G E R ∧
                Cont R P A ∧ Cont A L C ∧ Cont L N read ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier ledgerRoute readPkg
  obtain ⟨gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, hUnary, cUnary,
    qUnary, nUnary, generatorEqualityRoute, recursorPurityRoute, classifierRoute,
    provenancePkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed lUnary nUnary ledgerRoute
  exact
    ⟨gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, hUnary, cUnary, qUnary, nUnary,
      readUnary, generatorEqualityRoute, recursorPurityRoute, classifierRoute, ledgerRoute,
      provenancePkg, readPkg⟩

end BEDC.Derived.TheorySelfClassifierUp
