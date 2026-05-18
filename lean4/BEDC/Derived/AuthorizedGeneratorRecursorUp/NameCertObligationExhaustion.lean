import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorNameCertObligationExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N route outputRoute terminalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E route ->
        Cont O A outputRoute ->
          Cont outputRoute N terminalRoute ->
            PkgSig bundle terminalRoute pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                    hsame row terminalRoute)
                (fun row : BHist =>
                  hsame row O ∨ hsame row A ∨ hsame row N ∨ hsame row terminalRoute)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ PkgSig bundle terminalRoute pkg ∧
                    hsame row terminalRoute)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier sourceRoute outputRouteCont terminalRouteCont terminalPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      sameTransport, provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryI unaryE sourceRoute
  have outputRouteUnary : UnaryHistory outputRoute :=
    unary_cont_closed unaryO unaryA outputRouteCont
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed outputRouteUnary unaryN terminalRouteCont
  have carrierCopy :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
        _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
        sameTransport, provenancePkg⟩
  have sourceTerminal :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row terminalRoute) terminalRoute := by
    exact ⟨carrierCopy, hsame_refl terminalRoute⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalRoute sourceTerminal
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.right))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, terminalPkg, source.right⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
