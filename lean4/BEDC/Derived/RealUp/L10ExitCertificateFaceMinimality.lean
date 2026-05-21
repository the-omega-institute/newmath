import BEDC.Derived.RealUp.L10CurrentPhaseExitLocalThreshold

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10ExitCertificateFaceMinimality [AskSetup] [PackageSetup]
    {dyadic stream regular real support audit endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        UnaryHistory regular ->
          UnaryHistory real ->
            Cont dyadic stream support ->
              Cont support regular audit ->
                Cont audit real endpoint ->
                  PkgSig bundle endpoint pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regular ∨
                            hsame row real ∨ hsame row support ∨ hsame row endpoint)
                        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                        hsame ∧
                      UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
                        UnaryHistory real ∧ UnaryHistory support ∧ UnaryHistory audit ∧
                          UnaryHistory endpoint ∧ Cont dyadic stream support ∧
                            Cont support regular audit ∧ Cont audit real endpoint ∧
                              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro dyadicUnary streamUnary regularUnary realUnary supportRoute auditRoute endpointRoute
    endpointPkg
  have supportUnary : UnaryHistory support :=
    unary_cont_closed dyadicUnary streamUnary supportRoute
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed supportUnary regularUnary auditRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed auditUnary realUnary endpointRoute
  have sourceAtEndpoint : hsame endpoint endpoint ∧ UnaryHistory endpoint :=
    ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regular ∨ hsame row real ∨
              hsame row support ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regularUnary, realUnary, supportUnary, auditUnary,
      endpointUnary, supportRoute, auditRoute, endpointRoute, endpointPkg⟩

end BEDC.Derived.RealUp
