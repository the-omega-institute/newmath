import BEDC.Derived.OnticAdequacyAuditUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.OnticAdequacyAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem OnticAdequacyAudit_semantic_name_certificate [AskSetup] [PackageSetup]
    {O M S R E K L H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    onticAdequacyAuditFields (OnticAdequacyAuditUp.mk O M S R E K L H C P N) =
        [O, M, S, R, E, K, L, H, C, P, N] →
      Cont O M K →
        Cont S R E →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row K ∧
                  ∃ packet : OnticAdequacyAuditUp,
                    packet = OnticAdequacyAuditUp.mk O M S R E K L H C P N ∧
                      onticAdequacyAuditFields packet = [O, M, S, R, E, K, L, H, C, P, N])
              (fun row : BHist => Cont O M row ∧ Cont S R E)
              (fun row : BHist => hsame row K ∧ PkgSig bundle N pkg ∧ hsame H H)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact sourceAuditClassifier streamReadbackReal packageName
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨K, hsame_refl K,
            OnticAdequacyAuditUp.mk O M S R E K L H C P N, rfl, fieldsExact⟩
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
      intro row source
      cases source.left
      exact ⟨sourceAuditClassifier, streamReadbackReal⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, packageName, hsame_refl H⟩
  }

end BEDC.Derived.OnticAdequacyAuditUp
