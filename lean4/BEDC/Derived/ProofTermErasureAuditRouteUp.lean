import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProofTermErasureAuditRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProofTermErasureAuditRoute_erased_cont_replay
    {P E C R P' E' C' R' : BHist} (hP : hsame P P') (hC : hsame C C')
    (hR : hsame R R') (erasure : Cont P C E) (erasure' : Cont P' C' E') :
    hsame (append E R) (append E' R') := by
  cases hP
  cases hC
  cases hR
  cases erasure
  cases erasure'
  rfl

theorem ProofTermErasureAuditRoute_erased_replay_determinacy
    {P E T C R _S H Q N P' E' T' C' R' _S' H' Q' N' : BHist} (hP : hsame P P')
    (hT : hsame T T') (hC : hsame C C') (hR : hsame R R') (hH : hsame H H')
    (hQ : hsame Q Q') (hN : hsame N N') (erasure : Cont P C E)
    (erasure' : Cont P' C' E') :
    hsame
      (append E (append T (append C (append R (append H (append Q N))))))
      (append E' (append T' (append C' (append R' (append H' (append Q' N')))))) := by
  cases hP
  cases hT
  cases hC
  cases hR
  cases hH
  cases hQ
  cases hN
  cases erasure
  cases erasure'
  rfl

theorem ProofTermErasureAuditRoute_namecert_obligations [AskSetup] [PackageSetup]
    {P E T C R S _H _Q _N audit packageRow : BHist} {m : BMark}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Ext P m T →
      UnaryHistory P →
        UnaryHistory C →
          UnaryHistory R →
            UnaryHistory S →
              Cont P C E →
                Cont E R audit →
                  Cont audit S packageRow →
                    PkgSig bundle packageRow pkg →
                      UnaryHistory E ∧ UnaryHistory audit ∧ UnaryHistory packageRow ∧
                        Cont P C E ∧ Cont E R audit ∧ Cont audit S packageRow ∧
                          PkgSig bundle packageRow pkg := by
  -- BEDC touchpoint anchor: BHist BMark Ext Cont Pkg ProbeBundle UnaryHistory
  intro typing proofUnary erasureUnary subjectReductionUnary auditStampUnary proofErasure
    erasedAudit auditPackage packagePkg
  cases typing
  · have erasedUnary : UnaryHistory E :=
      unary_cont_closed proofUnary erasureUnary proofErasure
    have auditUnary : UnaryHistory audit :=
      unary_cont_closed erasedUnary subjectReductionUnary erasedAudit
    have packageUnary : UnaryHistory packageRow :=
      unary_cont_closed auditUnary auditStampUnary auditPackage
    exact
      ⟨erasedUnary, auditUnary, packageUnary, proofErasure, erasedAudit, auditPackage,
        packagePkg⟩
  · have erasedUnary : UnaryHistory E :=
      unary_cont_closed proofUnary erasureUnary proofErasure
    have auditUnary : UnaryHistory audit :=
      unary_cont_closed erasedUnary subjectReductionUnary erasedAudit
    have packageUnary : UnaryHistory packageRow :=
      unary_cont_closed auditUnary auditStampUnary auditPackage
    exact
      ⟨erasedUnary, auditUnary, packageUnary, proofErasure, erasedAudit, auditPackage,
        packagePkg⟩

end BEDC.Derived.ProofTermErasureAuditRouteUp
