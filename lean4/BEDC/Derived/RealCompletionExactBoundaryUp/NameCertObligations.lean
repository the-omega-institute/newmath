import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryNameCertObligations
    [AskSetup] [PackageSetup]
    {limitSeal classifier witness synchronizer window readback dyadic terminal transport replay
      provenance name sealClassifier witnessBudget streamReg terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory limitSeal ->
      UnaryHistory classifier ->
        UnaryHistory witness ->
          UnaryHistory synchronizer ->
            UnaryHistory window ->
              UnaryHistory readback ->
                UnaryHistory dyadic ->
                  UnaryHistory terminal ->
                    Cont limitSeal classifier sealClassifier ->
                      Cont witness synchronizer witnessBudget ->
                        Cont window readback streamReg ->
                          Cont dyadic terminal terminalRead ->
                            PkgSig bundle terminalRead pkg ->
                              realCompletionExactBoundaryFields
                                  (RealCompletionExactBoundaryUp.mk limitSeal classifier
                                    witness synchronizer window readback dyadic terminal
                                    transport replay provenance name) =
                                [limitSeal, classifier, witness, synchronizer, window,
                                  readback, dyadic, terminal, transport, replay, provenance,
                                  name] /\
                                UnaryHistory sealClassifier /\
                                  UnaryHistory witnessBudget /\ UnaryHistory streamReg /\
                                    UnaryHistory terminalRead /\
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row terminalRead /\ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row sealClassifier \/
                                            hsame row witnessBudget \/
                                              hsame row streamReg \/
                                                hsame row terminalRead)
                                        (fun row : BHist =>
                                          PkgSig bundle terminalRead pkg /\
                                            hsame row terminalRead)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro unaryLimitSeal unaryClassifier unaryWitness unarySynchronizer unaryWindow
    unaryReadback unaryDyadic unaryTerminal sealRoute witnessRoute streamRoute
    terminalRoute terminalPkg
  have unarySealClassifier : UnaryHistory sealClassifier :=
    unary_cont_closed unaryLimitSeal unaryClassifier sealRoute
  have unaryWitnessBudget : UnaryHistory witnessBudget :=
    unary_cont_closed unaryWitness unarySynchronizer witnessRoute
  have unaryStreamReg : UnaryHistory streamReg :=
    unary_cont_closed unaryWindow unaryReadback streamRoute
  have unaryTerminalRead : UnaryHistory terminalRead :=
    unary_cont_closed unaryDyadic unaryTerminal terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead /\ UnaryHistory row)
        (fun row : BHist =>
          hsame row sealClassifier \/ hsame row witnessBudget \/ hsame row streamReg \/
            hsame row terminalRead)
        (fun row : BHist => PkgSig bundle terminalRead pkg /\ hsame row terminalRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro terminalRead ⟨hsame_refl terminalRead, unaryTerminalRead⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨terminalPkg, source.left⟩
    }
  exact
    ⟨rfl, unarySealClassifier, unaryWitnessBudget, unaryStreamReg, unaryTerminalRead,
      cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
