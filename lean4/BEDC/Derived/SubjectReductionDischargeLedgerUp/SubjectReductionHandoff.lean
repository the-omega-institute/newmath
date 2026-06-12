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

theorem SubjectReductionDischargeLedgerSubjectReductionHandoff [AskSetup] [PackageSetup]
    {beta appArg lambdaDomain piDomain route transport replay provenance name routeRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionDischargeLedgerCarrier beta appArg lambdaDomain piDomain route
        transport replay provenance name bundle pkg ->
      Cont route replay routeRead ->
        Cont routeRead transport replayRead ->
          PkgSig bundle replayRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row beta ∨ hsame row appArg ∨ hsame row lambdaDomain ∨
                    hsame row piDomain ∨ hsame row route ∨ hsame row replay ∨
                      hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont beta appArg route ∧
                    Cont lambdaDomain piDomain replay ∧ Cont route replay routeRead ∧
                      Cont routeRead transport replayRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle replayRead pkg)
                hsame ∧
              UnaryHistory routeRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeReplay routeTransport replayPkg
  obtain ⟨_routeUnary, _replayUnary, _transportUnary, routeReadUnary, replayReadUnary,
    betaRoute, lambdaReplay, routeReplay', routeTransport', provenancePkg, replayPkg'⟩ :=
      SubjectReductionDischargeLedgerCarrier_route_handoff carrier routeReplay routeTransport
        replayPkg
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, betaRoute, lambdaReplay, routeReplay', routeTransport',
            provenancePkg, replayPkg'⟩
    }
  · exact ⟨routeReadUnary, replayReadUnary⟩

end BEDC.Derived.SubjectReductionDischargeLedgerUp
