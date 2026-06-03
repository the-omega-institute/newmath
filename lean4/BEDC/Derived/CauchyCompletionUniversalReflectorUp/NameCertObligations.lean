import BEDC.Derived.CauchyCompletionUniversalReflectorUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionUniversalReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionUniversalReflectorNamecertObligations [AskSetup] [PackageSetup]
    {source reflector functor extension inclusion stream regular dyadic real transport replay
      provenance localName sourceRead reflectorRead extensionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory stream ->
        UnaryHistory regular ->
          UnaryHistory dyadic ->
            UnaryHistory reflector ->
              UnaryHistory functor ->
                UnaryHistory extension ->
                  UnaryHistory inclusion ->
                    UnaryHistory real ->
                      Cont source stream sourceRead ->
                        Cont sourceRead reflector reflectorRead ->
                          Cont reflectorRead functor extensionRead ->
                            Cont extensionRead real realRead ->
                              PkgSig bundle provenance pkg ->
                                PkgSig bundle localName pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row realRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row source ∨ hsame row reflector ∨
                                          hsame row functor ∨ hsame row extension ∨
                                            hsame row inclusion ∨ hsame row stream ∨
                                              hsame row regular ∨ hsame row dyadic ∨
                                                hsame row real ∨ hsame row realRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory sourceRead ∧
                                      UnaryHistory reflectorRead ∧
                                        UnaryHistory extensionRead ∧
                                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro sourceUnary streamUnary _regularUnary _dyadicUnary reflectorUnary functorUnary
    _extensionUnary _inclusionUnary realUnary sourceRoute reflectorRoute extensionRoute
    realRoute provenancePkg localNamePkg
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary streamUnary sourceRoute
  have reflectorReadUnary : UnaryHistory reflectorRead :=
    unary_cont_closed sourceReadUnary reflectorUnary reflectorRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed reflectorReadUnary functorUnary extensionRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed extensionReadUnary realUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row reflector ∨ hsame row functor ∨
              hsame row extension ∨ hsame row inclusion ∨ hsame row stream ∨
                hsame row regular ∨ hsame row dyadic ∨ hsame row real ∨
                  hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        intro _row _other sameRows sourceSpec
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceSpec.left,
            unary_transport sourceSpec.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceSpec
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceSpec.left))))))))
    ledger_sound := by
      intro _row sourceSpec
      exact ⟨sourceSpec.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sourceReadUnary, reflectorReadUnary, extensionReadUnary, realReadUnary⟩

end BEDC.Derived.CauchyCompletionUniversalReflectorUp
