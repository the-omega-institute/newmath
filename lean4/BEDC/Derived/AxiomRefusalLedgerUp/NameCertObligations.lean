import BEDC.Derived.AxiomRefusalLedgerUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AxiomRefusalLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomRefusalLedger_namecert_obligations [AskSetup] [PackageSetup]
    {A S Q F R G H C P N nameRead alternativeRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory S ->
        UnaryHistory Q ->
          UnaryHistory F ->
            UnaryHistory R ->
              UnaryHistory G ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont A S nameRead ->
                      Cont Q F alternativeRead ->
                        Cont R G auditRead ->
                          hsame H BHist.Empty ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row N ∧ Cont A S nameRead ∧
                                    Cont Q F alternativeRead ∧ Cont R G auditRead ∧
                                      hsame H BHist.Empty)
                                (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                                hsame ∧ UnaryHistory nameRead ∧
                                UnaryHistory alternativeRead ∧ UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryA unaryS unaryQ unaryF unaryR unaryG _unaryC unaryN nameRoute alternativeRoute
    auditRoute transportEmpty provenancePkg
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed unaryA unaryS nameRoute
  have alternativeReadUnary : UnaryHistory alternativeRead :=
    unary_cont_closed unaryQ unaryF alternativeRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryR unaryG auditRoute
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row N ∧ Cont A S nameRead ∧ Cont Q F alternativeRead ∧
            Cont R G auditRead ∧ hsame H BHist.Empty)
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
      exact ⟨source.left, nameRoute, alternativeRoute, auditRoute, transportEmpty⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, nameReadUnary, alternativeReadUnary, auditReadUnary⟩

end BEDC.Derived.AxiomRefusalLedgerUp
