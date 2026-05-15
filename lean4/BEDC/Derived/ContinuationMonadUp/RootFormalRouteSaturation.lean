import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_formal_route_saturation [AskSetup] [PackageSetup]
    {A B C f g u H K L N rootRead formalRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N →
      Cont L N rootRead →
        Cont rootRead N formalRead →
          Cont formalRead K auditRead →
            PkgSig bundle auditRead pkg →
              UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
                UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
                  UnaryHistory N ∧ UnaryHistory rootRead ∧ UnaryHistory formalRead ∧
                    UnaryHistory auditRead ∧ Cont A f B ∧ Cont B g C ∧
                      Cont f g K ∧ Cont K u L ∧ Cont L N rootRead ∧
                        Cont rootRead N formalRead ∧ Cont formalRead K auditRead ∧
                          hsame N L ∧ PkgSig bundle auditRead pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row auditRead ∧ Cont L N rootRead ∧
                                  Cont rootRead N formalRead ∧ Cont formalRead K auditRead)
                              (fun row : BHist =>
                                hsame row auditRead ∧ PkgSig bundle auditRead pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont hsame
  intro carrier rootRoute formalRoute auditRoute auditPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryRootRead : UnaryHistory rootRead :=
    unary_cont_closed unaryL unaryN rootRoute
  have unaryFormalRead : UnaryHistory formalRead :=
    unary_cont_closed unaryRootRead unaryN formalRoute
  have unaryAuditRead : UnaryHistory auditRead :=
    unary_cont_closed unaryFormalRead unaryK auditRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row auditRead ∧ Cont L N rootRead ∧ Cont rootRead N formalRead ∧
            Cont formalRead K auditRead)
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro auditRead (And.intro (hsame_refl auditRead) unaryAuditRead)
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, rootRoute, formalRoute, auditRoute⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.left auditPkg
    }
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL, unaryN,
      unaryRootRead, unaryFormalRead, unaryAuditRead, routeB, routeC, routeK, routeL,
      rootRoute, formalRoute, auditRoute, sameEndpoint, auditPkg, cert⟩

end BEDC.Derived.ContinuationMonadUp
