import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def normalFormConsistencySealFields : NormalFormConsistencySealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalFormConsistencySealUp.mk T F N K X H C P L => [T, F, N, K, X, H, C, P, L]

theorem NormalFormConsistencySealCriticalPairRoute [AskSetup] [PackageSetup]
    {T F N K X H C P L criticalRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    normalFormConsistencySealFields (NormalFormConsistencySealUp.mk T F N K X H C P L) =
        [T, F, N, K, X, H, C, P, L] →
      UnaryHistory K →
        UnaryHistory X →
          UnaryHistory C →
            Cont K X criticalRead →
              Cont criticalRead C residualRead →
                PkgSig bundle P pkg →
                  PkgSig bundle L pkg →
                    SemanticNameCert
                          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
                              hsame row X ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                hsame row L ∨ hsame row criticalRead ∨
                                  hsame row residualRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont K X criticalRead ∧
                              Cont criticalRead C residualRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle L pkg)
                          hsame ∧
                        UnaryHistory criticalRead ∧ UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldsExact unaryK unaryX unaryC criticalRoute residualRoute provenancePkg localNamePkg
  cases fieldsExact
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed unaryK unaryX criticalRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed criticalUnary unaryC residualRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                hsame row criticalRead ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K X criticalRead ∧
              Cont criticalRead C residualRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro residualRead ⟨hsame_refl residualRead, residualUnary⟩
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
      exact ⟨source.right, criticalRoute, residualRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, criticalUnary, residualUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
