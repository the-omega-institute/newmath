import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealVisionHandoff [AskSetup] [PackageSetup]
    {T F N K X H C P L closedRead boundaryRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory L →
                      Cont T K closedRead →
                        Cont X C boundaryRead →
                          Cont closedRead L namedRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle L pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row closedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row F ∨ hsame row N ∨
                                        hsame row K ∨ hsame row X ∨ hsame row closedRead ∨
                                          hsame row boundaryRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle L pkg)
                                    hsame ∧
                                  UnaryHistory closedRead ∧ UnaryHistory boundaryRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro tUnary _fUnary _nUnary kUnary xUnary _hUnary cUnary _pUnary lUnary closedRoute
    boundaryRoute namedRoute provenancePkg localPkg
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed tUnary kUnary closedRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed xUnary cUnary boundaryRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed closedUnary lUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row closedRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closedRead ⟨hsame_refl closedRead, closedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localPkg⟩
  }
  exact ⟨cert, closedUnary, boundaryUnary, namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
