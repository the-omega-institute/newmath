import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryRoadmapOffTableRefusal [AskSetup] [PackageSetup]
    {W R D E H streamRead classifierRead boundaryRead terminalRead forbidden : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory D →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory H →
              Cont W D streamRead →
                Cont streamRead R classifierRead →
                  Cont classifierRead E boundaryRead →
                    Cont boundaryRead H terminalRead →
                      PkgSig bundle terminalRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row terminalRead ∧ UnaryHistory row ∧
                                PkgSig bundle row pkg)
                            (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                            (fun row : BHist => PkgSig bundle row pkg ∧
                              hsame row terminalRead)
                            hsame ∧
                          (Cont terminalRead (BHist.e1 forbidden) terminalRead →
                            False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro windowUnary dyadicUnary regseqUnary realUnary terminalFaceUnary streamRoute
    classifierRoute boundaryRoute terminalRoute terminalPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary dyadicUnary streamRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed streamUnary regseqUnary classifierRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed classifierUnary realUnary boundaryRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed boundaryUnary terminalFaceUnary terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row terminalRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary, terminalPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceRow.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, sourceRow.left⟩
  }
  have refusal : Cont terminalRead (BHist.e1 forbidden) terminalRead → False := by
    intro offTableRoute
    have suffixEmpty : hsame (BHist.e1 forbidden) BHist.Empty :=
      cont_right_unit_unique offTableRoute
    exact not_hsame_e1_empty suffixEmpty
  exact ⟨cert, refusal⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
