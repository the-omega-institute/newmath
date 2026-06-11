import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_candidate_sn_source_scope
    [AskSetup] [PackageSetup] {S U V B R G K H C P N substRead betaRead candidateRead
      ledgerRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont S V substRead ->
        Cont B R betaRead ->
          Cont substRead betaRead candidateRead ->
            Cont candidateRead K ledgerRead ->
              Cont ledgerRead N sourceRead ->
                PkgSig bundle sourceRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row U ∨ hsame row V ∨ hsame row B ∨
                          hsame row R ∨ hsame row G ∨ hsame row K ∨ hsame row N ∨
                            hsame row sourceRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S V substRead ∧ Cont B R betaRead ∧
                          Cont substRead betaRead candidateRead ∧
                            Cont candidateRead K ledgerRead ∧ Cont ledgerRead N sourceRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle sourceRead pkg)
                      hsame ∧
                    UnaryHistory substRead ∧ UnaryHistory betaRead ∧
                      UnaryHistory candidateRead ∧ UnaryHistory ledgerRead ∧
                        UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier substRoute betaRoute candidateRoute ledgerRoute sourceRoute sourcePkg
  obtain ⟨SUnary, _UUnary, VUnary, BUnary, RUnary, _GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, NUnary, _shiftSubstitution, _generatorPackage, _betaCarrierRoute,
    pkgSig⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed SUnary VUnary substRoute
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed substUnary betaUnary candidateRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed candidateUnary KUnary ledgerRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed ledgerUnary NUnary sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row V ∨ hsame row B ∨ hsame row R ∨
              hsame row G ∨ hsame row K ∨ hsame row N ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S V substRead ∧ Cont B R betaRead ∧
              Cont substRead betaRead candidateRead ∧ Cont candidateRead K ledgerRead ∧
                Cont ledgerRead N sourceRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
        have otherSame : hsame _ sourceRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory _ :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, substRoute, betaRoute, candidateRoute, ledgerRoute, sourceRoute,
          pkgSig, sourcePkg⟩
  }
  exact ⟨cert, substUnary, betaUnary, candidateUnary, ledgerUnary, sourceUnary⟩

end BEDC.Derived.MetaCICClosureTraceUp
