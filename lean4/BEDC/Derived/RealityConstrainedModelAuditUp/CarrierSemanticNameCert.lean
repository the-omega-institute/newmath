import BEDC.Derived.RealityConstrainedModelAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedModelAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedModelAuditCarrierSemanticNameCert [AskSetup] [PackageSetup]
    {H Pi O M C T L F S auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realityConstrainedModelAuditFields (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
        [H, Pi, O, M, C, T, L, F, S] →
      Cont H Pi O →
        Cont O M auditRead →
          PkgSig bundle S pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row auditRead ∧
                  ∃ packet : RealityConstrainedModelAuditUp,
                    packet = RealityConstrainedModelAuditUp.mk H Pi O M C T L F S ∧
                      realityConstrainedModelAuditFields packet =
                        [H, Pi, O, M, C, T, L, F, S])
              (fun row : BHist => Cont H Pi O ∧ Cont O M row)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle S pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact sourceObservation auditRoute strengthPkg
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨auditRead, hsame_refl auditRead,
            RealityConstrainedModelAuditUp.mk H Pi O M C T L F S, rfl, fieldsExact⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨sourceObservation, auditRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, strengthPkg⟩
  }

end BEDC.Derived.RealityConstrainedModelAuditUp
