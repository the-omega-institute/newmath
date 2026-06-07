import BEDC.Derived.SubjectReductionDischargeLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubjectReductionDischargeLedgerCarrier [AskSetup] [PackageSetup]
    (beta appArg lambdaDomain piDomain route transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory beta ∧ UnaryHistory appArg ∧ UnaryHistory lambdaDomain ∧
    UnaryHistory piDomain ∧ UnaryHistory route ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont beta appArg route ∧ Cont lambdaDomain piDomain replay ∧
          Cont route transport provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem SubjectReductionDischargeLedgerCarrier_route_handoff [AskSetup] [PackageSetup]
    {beta appArg lambdaDomain piDomain route transport replay provenance name routeRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeLedgerCarrier beta appArg lambdaDomain piDomain route
        transport replay provenance name bundle pkg →
      Cont route replay routeRead →
        Cont routeRead transport replayRead →
          PkgSig bundle replayRead pkg →
            UnaryHistory route ∧ UnaryHistory replay ∧ UnaryHistory transport ∧
              UnaryHistory routeRead ∧ UnaryHistory replayRead ∧
                Cont beta appArg route ∧ Cont lambdaDomain piDomain replay ∧
                  Cont route replay routeRead ∧ Cont routeRead transport replayRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier routeReplay routeTransport replayPkg
  obtain ⟨_unaryBeta, _unaryAppArg, _unaryLambdaDomain, _unaryPiDomain, unaryRoute,
    unaryTransport, unaryReplay, _unaryProvenance, _unaryName, betaRoute, lambdaReplay,
    _routeTransport, provenancePkg, _namePkg⟩ := carrier
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryRoute unaryReplay routeReplay
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed routeReadUnary unaryTransport routeTransport
  exact
    ⟨unaryRoute, unaryReplay, unaryTransport, routeReadUnary, replayReadUnary,
      betaRoute, lambdaReplay, routeReplay, routeTransport, provenancePkg, replayPkg⟩

theorem SubjectReductionDischargeLedgerConditionalNormalization [AskSetup] [PackageSetup]
    {beta appArg lambdaDomain piDomain route transport replay provenance name routeRead
      replayRead normalizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeLedgerCarrier beta appArg lambdaDomain piDomain route
        transport replay provenance name bundle pkg →
      Cont route replay routeRead →
        Cont routeRead transport replayRead →
          Cont replayRead provenance normalizedRead →
            PkgSig bundle normalizedRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row normalizedRead ∧ Cont replayRead provenance normalizedRead)
                  (fun row : BHist =>
                    hsame row beta ∨ hsame row appArg ∨ hsame row lambdaDomain ∨
                      hsame row piDomain ∨ hsame row route ∨ hsame row replay ∨
                        hsame row transport ∨ hsame row provenance ∨ hsame row name ∨
                          hsame row normalizedRead)
                  (fun row : BHist =>
                    hsame row normalizedRead ∧ Cont beta appArg route ∧
                      Cont lambdaDomain piDomain replay ∧ Cont route replay routeRead ∧
                        Cont routeRead transport replayRead ∧
                          Cont replayRead provenance normalizedRead)
                  hsame ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle normalizedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier routeReplay routeTransport replayProvenance normalizedPkg
  obtain ⟨_unaryBeta, _unaryAppArg, _unaryLambdaDomain, _unaryPiDomain, _unaryRoute,
    _unaryTransport, _unaryReplay, _unaryProvenance, _unaryName, betaRoute,
    lambdaReplay, _routeTransport, provenancePkg, _namePkg⟩ := carrier
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro normalizedRead (And.intro (hsame_refl normalizedRead) replayProvenance)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          constructor
          · exact hsame_trans (hsame_symm sameRows) source.left
          · cases sameRows
            exact source.right
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.left, betaRoute, lambdaReplay, routeReplay, routeTransport, source.right⟩
    }
  · exact And.intro provenancePkg normalizedPkg

end BEDC.Derived.SubjectReductionDischargeLedgerUp
