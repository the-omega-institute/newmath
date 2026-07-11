import BEDC.Derived.CompactMetricProductUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactMetricProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactMetricProductComponentHandoff [AskSetup] [PackageSetup]
    {X Y M P T L H C Q N productNet pairedLimit replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory Y →
        UnaryHistory M →
          UnaryHistory P →
            UnaryHistory T →
              UnaryHistory L →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory Q →
                      UnaryHistory N →
                        Cont X Y P →
                          Cont P M productNet →
                            Cont productNet L pairedLimit →
                              Cont pairedLimit C replay →
                                PkgSig bundle Q pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row replay ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row Y ∨ hsame row M ∨
                                            hsame row P ∨ hsame row T ∨
                                              hsame row L ∨ hsame row H ∨
                                                hsame row C ∨ hsame row Q ∨
                                                  hsame row N ∨ hsame row productNet ∨
                                                    hsame row pairedLimit ∨
                                                      hsame row replay)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont X Y P ∧
                                            Cont P M productNet ∧
                                              Cont productNet L pairedLimit ∧
                                                Cont pairedLimit C replay ∧
                                                  PkgSig bundle Q pkg ∧
                                                    PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory productNet ∧
                                        UnaryHistory pairedLimit ∧
                                          UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro xUnary yUnary mUnary pUnary _tUnary lUnary _hUnary cUnary _qUnary _nUnary
    productRoute netRoute limitRoute replayRoute compactPkg namePkg
  have productNetUnary : UnaryHistory productNet :=
    unary_cont_closed pUnary mUnary netRoute
  have pairedLimitUnary : UnaryHistory pairedLimit :=
    unary_cont_closed productNetUnary lUnary limitRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed pairedLimitUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row M ∨ hsame row P ∨
              hsame row T ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                hsame row Q ∨ hsame row N ∨ hsame row productNet ∨
                  hsame row pairedLimit ∨ hsame row replay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X Y P ∧ Cont P M productNet ∧
              Cont productNet L pairedLimit ∧ Cont pairedLimit C replay ∧
                PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replay, hsame_refl replay, replayUnary⟩
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
                          (Or.inr
                            (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, productRoute, netRoute, limitRoute, replayRoute, compactPkg,
          namePkg⟩
  }
  exact ⟨cert, productNetUnary, pairedLimitUnary, replayUnary⟩

end BEDC.Derived.CompactMetricProductUp
