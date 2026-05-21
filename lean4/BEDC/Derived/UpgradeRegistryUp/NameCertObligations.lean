import BEDC.Derived.UpgradeRegistryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UpgradeRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpgradeRegistryNameCertObligations [AskSetup] [PackageSetup]
    {T S Nx F B A R H C P L statusRead blockerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T -> UnaryHistory S -> UnaryHistory Nx -> UnaryHistory F -> UnaryHistory B ->
      UnaryHistory A -> UnaryHistory R -> UnaryHistory C -> UnaryHistory L ->
        Cont S Nx statusRead -> Cont F B blockerRead -> Cont C L namedRead ->
          PkgSig bundle namedRead pkg ->
            upgradeRegistryFields (UpgradeRegistryUp.mk T S Nx F B A R H C P L) =
                [T, S, Nx, F, B, A, R, H, C, P, L] ∧
              UnaryHistory statusRead ∧ UnaryHistory blockerRead ∧ UnaryHistory namedRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row statusRead ∨ hsame row blockerRead ∨ hsame row namedRead)
                  (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro _TUnary SUnary NxUnary FUnary BUnary _AUnary _RUnary CUnary LUnary
    statusCont blockerCont namedCont namedPkg
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed SUnary NxUnary statusCont
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed FUnary BUnary blockerCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed CUnary LUnary namedCont
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row statusRead ∨ hsame row blockerRead ∨ hsame row namedRead)
        (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead sourceNamed
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨namedPkg, source.left⟩
    }
  exact ⟨rfl, statusUnary, blockerUnary, namedUnary, cert⟩

end BEDC.Derived.UpgradeRegistryUp
