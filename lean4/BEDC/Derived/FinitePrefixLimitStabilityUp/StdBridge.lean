import BEDC.Derived.FinitePrefixLimitStabilityUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FinitePrefixLimitStabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FinitePrefixLimitStabilityUp_StdBridge [AskSetup] [PackageSetup]
    {B W R D E H C P N BW WR RD DE terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → Cont B W BW → Cont BW R WR →
        Cont WR D RD → Cont RD E DE → Cont DE N terminal →
          PkgSig bundle terminal pkg →
            FieldFaithful.fields
                (FinitePrefixLimitStabilityUp.packet B W R D E H C P N) =
                [B, W, R, D, E, H, C, P, N] ∧
              UnaryHistory terminal ∧
                SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row BW ∨ hsame row WR ∨ hsame row RD ∨ hsame row DE ∨
                      hsame row terminal)
                  (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryB unaryW unaryR unaryD unaryE unaryN budgetWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalPkg
  have budgetWindowUnary : UnaryHistory BW :=
    unary_cont_closed unaryB unaryW budgetWindow
  have windowReadbackUnary : UnaryHistory WR :=
    unary_cont_closed budgetWindowUnary unaryR windowReadback
  have readbackToleranceUnary : UnaryHistory RD :=
    unary_cont_closed windowReadbackUnary unaryD readbackTolerance
  have toleranceSealUnary : UnaryHistory DE :=
    unary_cont_closed readbackToleranceUnary unaryE toleranceSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed toleranceSealUnary unaryN sealTerminal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row BW ∨ hsame row WR ∨ hsame row RD ∨ hsame row DE ∨
            hsame row terminal)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal ⟨hsame_refl terminal, terminalUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact ⟨rfl, terminalUnary, cert⟩

end BEDC.Derived.FinitePrefixLimitStabilityUp
