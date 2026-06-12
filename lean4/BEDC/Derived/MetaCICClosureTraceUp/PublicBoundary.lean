import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_public_boundary [AskSetup] [PackageSetup]
    {S U V B R G K H C P N candidateRead confluenceRead decisionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg →
      Cont (append (append S U) G) (append B R) candidateRead →
        Cont candidateRead K confluenceRead →
          Cont confluenceRead N publicRead →
            Cont K N decisionRead →
              PkgSig bundle publicRead pkg →
                PkgSig bundle decisionRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row U ∨ hsame row V ∨ hsame row B ∨
                          hsame row R ∨ hsame row G ∨ hsame row K ∨
                            hsame row candidateRead ∨ hsame row confluenceRead ∨
                              hsame row decisionRead ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧
                          Cont (append (append S U) G) (append B R) candidateRead ∧
                            Cont candidateRead K confluenceRead ∧
                              Cont confluenceRead N publicRead ∧
                                Cont K N decisionRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle publicRead pkg ∧
                                    PkgSig bundle decisionRead pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory confluenceRead ∧
                      UnaryHistory decisionRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute confluenceRoute publicRoute decisionRoute publicPkg decisionPkg
  obtain ⟨SUnary, UUnary, _VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
    provenancePkg⟩ := carrier
  have SUUnary : UnaryHistory (append S U) :=
    unary_append_closed SUnary UUnary
  have generatorUnary : UnaryHistory (append (append S U) G) :=
    unary_append_closed SUUnary GUnary
  have betaUnary : UnaryHistory (append B R) :=
    unary_append_closed BUnary RUnary
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed generatorUnary betaUnary candidateRoute
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed candidateUnary KUnary confluenceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed confluenceUnary NUnary publicRoute
  have decisionUnary : UnaryHistory decisionRead :=
    unary_cont_closed KUnary NUnary decisionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row V ∨ hsame row B ∨
              hsame row R ∨ hsame row G ∨ hsame row K ∨ hsame row candidateRead ∨
                hsame row confluenceRead ∨ hsame row decisionRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont (append (append S U) G) (append B R) candidateRead ∧
              Cont candidateRead K confluenceRead ∧ Cont confluenceRead N publicRead ∧
                Cont K N decisionRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle publicRead pkg ∧ PkgSig bundle decisionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, candidateRoute, confluenceRoute, publicRoute, decisionRoute,
          provenancePkg, publicPkg, decisionPkg⟩
  }
  exact ⟨cert, candidateUnary, confluenceUnary, decisionUnary, publicUnary⟩

end BEDC.Derived.MetaCICClosureTraceUp
