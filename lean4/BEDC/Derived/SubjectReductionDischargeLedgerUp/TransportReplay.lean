import BEDC.Derived.SubjectReductionDischargeLedgerUp.Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SubjectReductionDischargeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionDischargeLedgerTransportReplay [AskSetup] [PackageSetup]
    {beta appArg lambdaDomain piDomain route transport replay provenance name transportRead
      replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeLedgerCarrier beta appArg lambdaDomain piDomain route transport
        replay provenance name bundle pkg →
      Cont transport replay transportRead →
        Cont transportRead route replayRead →
          Cont replayRead name namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row beta ∨ hsame row appArg ∨ hsame row lambdaDomain ∨
                      hsame row piDomain ∨ hsame row route ∨ hsame row transport ∨
                        hsame row replay ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont transport replay transportRead ∧
                      Cont transportRead route replayRead ∧ Cont replayRead name namedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier transportRoute replayRoute namedRoute namedPkg
  obtain ⟨_betaUnary, _appArgUnary, _lambdaDomainUnary, _piDomainUnary, routeUnary,
    transportUnary, replayUnary, _provenanceUnary, nameUnary, _betaRoute, _lambdaReplay,
    _routeTransport, provenancePkg, _namePkg⟩ := carrier
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary replayUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary routeUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary nameUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
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
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, transportRoute, replayRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedReadUnary

end BEDC.Derived.SubjectReductionDischargeLedgerUp
