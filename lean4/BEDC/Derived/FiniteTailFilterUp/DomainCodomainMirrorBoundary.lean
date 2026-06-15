import BEDC.Derived.FiniteTailFilterUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_domain_codomain_mirror_boundary
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N domainRead codomainRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D domainRead ->
        Cont domainRead E codomainRead ->
          PkgSig bundle codomainRead pkg ->
            UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
              UnaryHistory domainRead ∧ UnaryHistory codomainRead ∧ hsame N E ∧
                Cont S D domainRead ∧ Cont domainRead E codomainRead ∧
                  PkgSig bundle codomainRead pkg := by
  -- BEDC touchpoint anchor: FiniteTailFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier domainRoute codomainRoute codomainPkg
  obtain ⟨unaryS, unaryD, _unaryB, unaryE, _unaryH, _unaryC, _routeR, _routeQ,
    sameN⟩ := carrier
  have domainUnary : UnaryHistory domainRead :=
    unary_cont_closed unaryS unaryD domainRoute
  have codomainUnary : UnaryHistory codomainRead :=
    unary_cont_closed domainUnary unaryE codomainRoute
  exact
    ⟨unaryS, unaryD, unaryE, domainUnary, codomainUnary, sameN, domainRoute,
      codomainRoute, codomainPkg⟩

theorem FiniteTailFilterDomainCodomainMirrorBoundary
    {S D R B Q E H C P N domainRead codomainRead mirrorRead : BHist} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D domainRead ->
        Cont R B codomainRead ->
          Cont domainRead codomainRead mirrorRead ->
            SemanticNameCert
                  (fun row : BHist => hsame row mirrorRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row domainRead ∨ hsame row codomainRead ∨ hsame row mirrorRead)
                  (fun row : BHist =>
                    hsame row mirrorRead ∧ Cont domainRead codomainRead mirrorRead)
                  hsame ∧
              UnaryHistory domainRead ∧ UnaryHistory codomainRead ∧
                UnaryHistory mirrorRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier domainRoute codomainRoute mirrorRoute
  obtain ⟨unaryS, unaryD, unaryB, _unaryE, _unaryH, _unaryC, routeR, _routeQ,
    _sameN⟩ := carrier
  have domainUnary : UnaryHistory domainRead :=
    unary_cont_closed unaryS unaryD domainRoute
  have codomainUnary : UnaryHistory codomainRead :=
    unary_cont_closed (unary_cont_closed unaryS unaryD routeR) unaryB codomainRoute
  have mirrorUnary : UnaryHistory mirrorRead :=
    unary_cont_closed domainUnary codomainUnary mirrorRoute
  have sourceAtMirror : hsame mirrorRead mirrorRead ∧ UnaryHistory mirrorRead :=
    ⟨hsame_refl mirrorRead, mirrorUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row mirrorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domainRead ∨ hsame row codomainRead ∨ hsame row mirrorRead)
          (fun row : BHist =>
            hsame row mirrorRead ∧ Cont domainRead codomainRead mirrorRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro mirrorRead sourceAtMirror
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, mirrorRoute⟩
  }
  exact ⟨cert, domainUnary, codomainUnary, mirrorUnary⟩

end BEDC.Derived.FiniteTailFilterUp
