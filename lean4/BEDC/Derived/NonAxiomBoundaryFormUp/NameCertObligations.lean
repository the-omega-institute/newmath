import BEDC.Derived.NonAxiomBoundaryFormUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NonAxiomBoundaryFormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NonAxiomBoundaryForm_namecert_obligations [AskSetup] [PackageSetup]
    {B K S G H C P N boundaryRead gateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory K ->
        UnaryHistory S ->
          UnaryHistory G ->
            UnaryHistory C ->
              UnaryHistory N ->
                Cont B K boundaryRead ->
                  Cont S G gateRead ->
                    hsame H BHist.Empty ->
                      PkgSig bundle P pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row N ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row N ∧ Cont B K boundaryRead ∧ Cont S G gateRead ∧
                              hsame H BHist.Empty)
                          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                          hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory gateRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryB unaryK unaryS unaryG _unaryC unaryN boundaryRoute gateRoute transportEmpty
    provenancePkg
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryB unaryK boundaryRoute
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed unaryS unaryG gateRoute
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row N ∧ Cont B K boundaryRead ∧ Cont S G gateRead ∧
            hsame H BHist.Empty)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
      exact ⟨source.left, boundaryRoute, gateRoute, transportEmpty⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, boundaryReadUnary, gateReadUnary⟩

end BEDC.Derived.NonAxiomBoundaryFormUp
