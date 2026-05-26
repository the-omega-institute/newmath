import BEDC.Derived.FiniteRealSectionUp.ObligationClosureCertificate

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteRealSection_StdBridge [AskSetup] [PackageSetup]
    {q W R D E _H C _P N qW qWR qWRD qWRDE terminal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory C → UnaryHistory N → Cont q W qW →
        Cont qW R qWR → Cont qWR D qWRD → Cont qWRD E qWRDE →
          Cont qWRDE N terminal → Cont terminal C publicRead →
            PkgSig bundle terminal pkg → PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨
                      hsame row qWRDE ∨ hsame row terminal ∨ hsame row publicRead)
                  (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                Cont q W qW ∧ Cont qW R qWR ∧ Cont qWR D qWRD ∧
                  Cont qWRD E qWRDE ∧ Cont qWRDE N terminal ∧
                    Cont terminal C publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryC unaryN requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalPublic terminalPkg publicPkg
  have requestWindowUnary : UnaryHistory qW :=
    unary_cont_closed unaryQ unaryW requestWindow
  have windowReadbackUnary : UnaryHistory qWR :=
    unary_cont_closed requestWindowUnary unaryR windowReadback
  have readbackToleranceUnary : UnaryHistory qWRD :=
    unary_cont_closed windowReadbackUnary unaryD readbackTolerance
  have toleranceSealUnary : UnaryHistory qWRDE :=
    unary_cont_closed readbackToleranceUnary unaryE toleranceSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed toleranceSealUnary unaryN sealTerminal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed terminalUnary unaryC terminalPublic
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row qW ∨ hsame row qWR ∨ hsame row qWRD ∨ hsame row qWRDE ∨
            hsame row terminal ∨ hsame row publicRead)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact
    ⟨cert, requestWindow, windowReadback, readbackTolerance, toleranceSeal, sealTerminal,
      terminalPublic⟩

end BEDC.Derived.FiniteRealSectionUp
