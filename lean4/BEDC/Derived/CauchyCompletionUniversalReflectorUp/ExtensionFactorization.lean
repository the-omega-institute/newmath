import BEDC.Derived.CauchyCompletionUniversalReflectorUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyCompletionUniversalReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionUniversalReflectorCarrier_extension_factorization
    [AskSetup] [PackageSetup]
    {source reflector functor extension inclusion window regseq dyadic real transport replay
      provenance name sourceRead reflectorRead functorRead extensionRead inclusionRead realRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory reflector ->
        UnaryHistory functor ->
          UnaryHistory extension ->
            UnaryHistory inclusion ->
              UnaryHistory real ->
                UnaryHistory transport ->
                  Cont source reflector sourceRead ->
                    Cont sourceRead functor reflectorRead ->
                      Cont reflectorRead extension functorRead ->
                        Cont functorRead inclusion extensionRead ->
                          Cont extensionRead real inclusionRead ->
                            Cont inclusionRead transport auditRead ->
                              PkgSig bundle provenance pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row source ∨ hsame row reflector ∨
                                        hsame row functor ∨ hsame row extension ∨
                                          hsame row inclusion ∨ hsame row real ∨
                                            hsame row sourceRead ∨ hsame row reflectorRead ∨
                                              hsame row functorRead ∨ hsame row extensionRead ∨
                                                hsame row inclusionRead ∨ hsame row auditRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont source reflector sourceRead ∧
                                          Cont sourceRead functor reflectorRead ∧
                                            Cont reflectorRead extension functorRead ∧
                                              Cont functorRead inclusion extensionRead ∧
                                                Cont extensionRead real inclusionRead ∧
                                                  PkgSig bundle provenance pkg)
                                    hsame ∧
                                  UnaryHistory sourceRead ∧ UnaryHistory reflectorRead ∧
                                    UnaryHistory functorRead ∧ UnaryHistory extensionRead ∧
                                      UnaryHistory inclusionRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unarySource unaryReflector unaryFunctor unaryExtension unaryInclusion unaryReal
    unaryTransport sourceRoute reflectorRoute functorRoute extensionRoute inclusionRoute
    realRoute provenancePkg
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unarySource unaryReflector sourceRoute
  have reflectorReadUnary : UnaryHistory reflectorRead :=
    unary_cont_closed sourceReadUnary unaryFunctor reflectorRoute
  have functorReadUnary : UnaryHistory functorRead :=
    unary_cont_closed reflectorReadUnary unaryExtension functorRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed functorReadUnary unaryInclusion extensionRoute
  have inclusionReadUnary : UnaryHistory inclusionRead :=
    unary_cont_closed extensionReadUnary unaryReal inclusionRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed inclusionReadUnary unaryTransport realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row reflector ∨ hsame row functor ∨
              hsame row extension ∨ hsame row inclusion ∨ hsame row real ∨
                hsame row sourceRead ∨ hsame row reflectorRead ∨ hsame row functorRead ∨
                  hsame row extensionRead ∨ hsame row inclusionRead ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source reflector sourceRead ∧
              Cont sourceRead functor reflectorRead ∧
                Cont reflectorRead extension functorRead ∧
                  Cont functorRead inclusion extensionRead ∧
                    Cont extensionRead real inclusionRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead ⟨hsame_refl auditRead, auditReadUnary⟩
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
        intro _row _other sameRows sourceAudit
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceAudit.left,
            unary_transport sourceAudit.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceAudit
      repeat right
      exact sourceAudit.left
    ledger_sound := by
      intro _row sourceAudit
      exact
        ⟨sourceAudit.right, sourceRoute, reflectorRoute, functorRoute, extensionRoute,
          inclusionRoute, provenancePkg⟩
  }
  exact
    ⟨cert, sourceReadUnary, reflectorReadUnary, functorReadUnary, extensionReadUnary,
      inclusionReadUnary, auditReadUnary⟩

end BEDC.Derived.CauchyCompletionUniversalReflectorUp
