import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ConsciousObserverStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ConsciousObserverStateCarrier [AskSetup] [PackageSetup]
    (observer state recognition ledger gap transport route provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
    UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory endpoint ∧
        Cont observer route endpoint ∧ Cont state route endpoint ∧
          Cont recognition ledger gap ∧ Cont transport provenance endpoint ∧
            PkgSig bundle endpoint pkg

theorem ConsciousObserverStateCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {observer state recognition ledger gap transport route provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConsciousObserverStateCarrier observer state recognition ledger gap transport route provenance
        name endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ConsciousObserverStateCarrier observer state recognition ledger gap transport route
              provenance name endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          Cont observer route row ∧ Cont state route row ∧ PkgSig bundle row pkg)
        (fun _row : BHist =>
          UnaryHistory observer ∧ UnaryHistory state ∧ UnaryHistory recognition ∧
            UnaryHistory ledger ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory endpoint)
        hsame := by
  intro carrier
  have observerUnary : UnaryHistory observer := carrier.left
  have stateUnary : UnaryHistory state := carrier.right.left
  have recognitionUnary : UnaryHistory recognition := carrier.right.right.left
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.left
  have gapUnary : UnaryHistory gap := carrier.right.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.right.left
  have routeUnary : UnaryHistory route := carrier.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.right.left
  have nameUnary : UnaryHistory name := carrier.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have observerRoute : Cont observer route endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have stateRoute : Cont state route endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _left _right same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _left _right same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      have same : hsame row endpoint := source.right
      cases same
      exact And.intro observerRoute (And.intro stateRoute endpointPkg)
    ledger_sound := by
      intro _row _source
      exact
        And.intro observerUnary
          (And.intro stateUnary
            (And.intro recognitionUnary
              (And.intro ledgerUnary
                (And.intro gapUnary
                  (And.intro transportUnary
                    (And.intro routeUnary
                      (And.intro provenanceUnary
                        (And.intro nameUnary endpointUnary))))))))
  }

end BEDC.Derived.ConsciousObserverStateUp
