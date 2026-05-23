import BEDC.Derived.ReviewAcceptanceGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReviewAcceptanceGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReviewAcceptanceGateNameCertObligations [AskSetup] [PackageSetup]
    {S D R A M K Q H C P N decisionApproval machineKernel namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S → UnaryHistory D → UnaryHistory A → UnaryHistory M →
      UnaryHistory K → UnaryHistory N → Cont S D decisionApproval →
        Cont M K machineKernel → Cont decisionApproval N namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row decisionApproval ∨ hsame row machineKernel ∨
                    hsame row namedRead)
                (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                hsame ∧
              List.Mem A
                (reviewAcceptanceGateFields
                  (ReviewAcceptanceGateUp.mk S D R A M K Q H C P N)) ∧
                List.Mem K
                  (reviewAcceptanceGateFields
                    (ReviewAcceptanceGateUp.mk S D R A M K Q H C P N)) ∧
                  UnaryHistory decisionApproval ∧ UnaryHistory machineKernel ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro proposalUnary decisionUnary acceptanceUnary machineUnary kernelUnary nameUnary
    decisionCont machineCont namedCont namedPkg
  have decisionApprovalUnary : UnaryHistory decisionApproval :=
    unary_cont_closed proposalUnary decisionUnary decisionCont
  have machineKernelUnary : UnaryHistory machineKernel :=
    unary_cont_closed machineUnary kernelUnary machineCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed decisionApprovalUnary nameUnary namedCont
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row decisionApproval ∨ hsame row machineKernel ∨ hsame row namedRead)
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
  exact
    ⟨cert,
      List.Mem.tail S
        (List.Mem.tail D
          (List.Mem.tail R (List.Mem.head [M, K, Q, H, C, P, N]))),
      List.Mem.tail S
        (List.Mem.tail D
          (List.Mem.tail R
            (List.Mem.tail A (List.Mem.tail M (List.Mem.head [Q, H, C, P, N]))))),
      decisionApprovalUnary, machineKernelUnary, namedReadUnary⟩

end BEDC.Derived.ReviewAcceptanceGateUp
