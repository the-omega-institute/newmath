import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_candidate_closedness_interface [AskSetup] [PackageSetup]
    {S U V B R G K H C P N candidateRead ledgerRead interfaceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont (append (append S U) G) (append B R) candidateRead ->
        Cont candidateRead K ledgerRead ->
          Cont ledgerRead N interfaceRead ->
            PkgSig bundle interfaceRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row interfaceRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row (append (append S U) G) ∨ hsame row (append B R) ∨
                      hsame row K ∨ hsame row N ∨ hsame row interfaceRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle interfaceRead pkg)
                  hsame ∧
                UnaryHistory candidateRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory interfaceRead ∧
                    Cont (append (append S U) G) (append B R) candidateRead ∧
                      Cont candidateRead K ledgerRead ∧ Cont ledgerRead N interfaceRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle interfaceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute ledgerRoute interfaceRoute interfacePkg
  obtain ⟨SUnary, UUnary, _VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
    pkgSig⟩ := carrier
  have SUUnary : UnaryHistory (append S U) :=
    unary_append_closed SUnary UUnary
  have generatorUnary : UnaryHistory (append (append S U) G) :=
    unary_append_closed SUUnary GUnary
  have betaUnary : UnaryHistory (append B R) :=
    unary_append_closed BUnary RUnary
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed generatorUnary betaUnary candidateRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed candidateUnary KUnary ledgerRoute
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed ledgerUnary NUnary interfaceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row interfaceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row (append (append S U) G) ∨ hsame row (append B R) ∨
              hsame row K ∨ hsame row N ∨ hsame row interfaceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle interfaceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro interfaceRead ⟨hsame_refl interfaceRead, interfaceUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgSig, interfacePkg⟩
  }
  exact
    ⟨cert, candidateUnary, ledgerUnary, interfaceUnary, candidateRoute, ledgerRoute,
      interfaceRoute, pkgSig, interfacePkg⟩

end BEDC.Derived.MetaCICClosureTraceUp
