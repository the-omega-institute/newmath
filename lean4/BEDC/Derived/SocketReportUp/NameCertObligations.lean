import BEDC.Derived.SocketReportUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SocketReportNameCertObligations [AskSetup] [PackageSetup]
    {site requestedSupply socketKind auditGate transport continuation provenance localName
      siteRead kindRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory site -> UnaryHistory requestedSupply -> UnaryHistory socketKind ->
      UnaryHistory auditGate -> UnaryHistory continuation -> UnaryHistory localName ->
        Cont site requestedSupply siteRead -> Cont socketKind auditGate kindRead ->
          Cont continuation localName namedRead -> PkgSig bundle namedRead pkg ->
            socketReportFields
                (SocketReportUp.mk site requestedSupply socketKind auditGate transport
                  continuation provenance localName) =
              [site, requestedSupply, socketKind, auditGate, transport, continuation,
                provenance, localName] ∧
              UnaryHistory siteRead ∧ UnaryHistory kindRead ∧ UnaryHistory namedRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row siteRead ∨ hsame row kindRead ∨ hsame row namedRead)
                  (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro siteUnary requestedSupplyUnary socketKindUnary auditGateUnary continuationUnary
    localNameUnary siteCont kindCont namedCont namedPkg
  have siteReadUnary : UnaryHistory siteRead :=
    unary_cont_closed siteUnary requestedSupplyUnary siteCont
  have kindReadUnary : UnaryHistory kindRead :=
    unary_cont_closed socketKindUnary auditGateUnary kindCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed continuationUnary localNameUnary namedCont
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row siteRead ∨ hsame row kindRead ∨ hsame row namedRead)
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
  exact ⟨rfl, siteReadUnary, kindReadUnary, namedReadUnary, cert⟩

end BEDC.Derived.SocketReportUp
