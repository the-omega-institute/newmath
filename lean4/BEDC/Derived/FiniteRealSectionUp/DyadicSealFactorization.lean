import BEDC.Derived.FiniteRealSectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteRealSection_dyadic_seal_factorization [AskSetup] [PackageSetup]
    {q W R D E N qW qWR qWRD qWRDE terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → Cont q W qW → Cont qW R qWR →
        Cont qWR D qWRD → Cont qWRD E qWRDE → Cont qWRDE N terminal →
          PkgSig bundle terminal pkg →
            hsame qWRDE (append (append (append (append q W) R) D) E) ∧
              hsame terminal (append qWRDE N) ∧
                SemanticNameCert
                  (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row qWRD ∨ hsame row qWRDE ∨ hsame row terminal)
                  (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalPkg
  have qWUnary : UnaryHistory qW :=
    unary_cont_closed unaryQ unaryW requestWindow
  have qWRUnary : UnaryHistory qWR :=
    unary_cont_closed qWUnary unaryR windowReadback
  have qWRDUnary : UnaryHistory qWRD :=
    unary_cont_closed qWRUnary unaryD readbackTolerance
  have qWRDEUnary : UnaryHistory qWRDE :=
    unary_cont_closed qWRDUnary unaryE toleranceSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed qWRDEUnary unaryN sealTerminal
  have sealExact : hsame qWRDE (append (append (append (append q W) R) D) E) := by
    cases requestWindow
    cases windowReadback
    cases readbackTolerance
    cases toleranceSeal
    rfl
  have terminalExact : hsame terminal (append qWRDE N) := by
    cases sealTerminal
    rfl
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist => hsame row qWRD ∨ hsame row qWRDE ∨ hsame row terminal)
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
        intro _row _other same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact ⟨sealExact, terminalExact, cert⟩

end BEDC.Derived.FiniteRealSectionUp
