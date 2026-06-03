import BEDC.Derived.RealUp.L10FaceStatusNoncollapse
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10CurrentPhaseExitAuditPullback [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalRead statusRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic →
      UnaryHistory stream →
        UnaryHistory regseq →
          UnaryHistory sealRow →
            UnaryHistory transport →
              UnaryHistory route →
                UnaryHistory provenance →
                  UnaryHistory localName →
                    Cont dyadic stream sourceRoute →
                      Cont sourceRoute regseq streamRoute →
                        Cont streamRoute sealRow regseqRoute →
                          Cont regseqRoute transport sealRoute →
                            Cont sealRoute localName interfaceRead →
                              Cont interfaceRead route terminalRead →
                                Cont terminalRead localName statusRead →
                                  Cont statusRead provenance auditRead →
                                    PkgSig bundle provenance pkg →
                                      PkgSig bundle auditRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row auditRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row dyadic ∨ hsame row stream ∨
                                                hsame row regseq ∨ hsame row sealRow ∨
                                                  hsame row statusRead ∨
                                                    hsame row auditRead)
                                            (fun row : BHist =>
                                              PkgSig bundle row pkg ∧
                                                Cont statusRead provenance auditRead)
                                            hsame ∧
                                          UnaryHistory auditRead ∧
                                            PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal
    terminalLocalNameStatus statusProvenanceAudit _provenancePkg auditPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed sealRouteUnary localNameUnary sealLocalNameInterface
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed interfaceUnary routeUnary interfaceRouteTerminal
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed terminalUnary localNameUnary terminalLocalNameStatus
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed statusUnary provenanceUnary statusProvenanceAudit
  have sourceAudit :
      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row) auditRead := by
    exact ⟨hsame_refl auditRead, auditUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row sealRow ∨ hsame row statusRead ∨ hsame row auditRead)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont statusRead provenance auditRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨auditPkg, statusProvenanceAudit⟩
  }
  exact ⟨cert, auditUnary, auditPkg⟩

end BEDC.Derived.RealUp
