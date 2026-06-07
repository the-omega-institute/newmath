import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricRealRouteBoundary [AskSetup] [PackageSetup]
    {X S M L D H C P N realRoute realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] →
      UnaryHistory L →
        UnaryHistory D →
          UnaryHistory P →
            Cont L D realRoute →
              Cont realRoute P realRead →
                PkgSig bundle P pkg →
                  PkgSig bundle realRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row D ∨ hsame row P ∨ hsame row realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont L D realRoute ∧
                            Cont realRoute P realRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle realRead pkg)
                        hsame ∧
                      UnaryHistory realRoute ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro fieldRows lUnary dUnary pUnary realRouteStep realReadStep provenancePkg realReadPkg
  cases fieldRows
  have realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed lUnary dUnary realRouteStep
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed realRouteUnary pUnary realReadStep
  constructor
  · exact {
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
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, realRouteStep, realReadStep, provenancePkg, realReadPkg⟩
    }
  · exact ⟨realRouteUnary, realReadUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
