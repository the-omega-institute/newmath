import BEDC.Derived.ReflectiveInquiryUp.LedgeredRoleCorrespondence
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ReflectiveInquiryClassifierAuditCertificate [AskSetup] [PackageSetup]
    {P F S K A R L H C Q N P' F' S' K' A' R' L' H' C' Q' N' bridge audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectiveInquiryClassifier P F S K A R L H C Q N P' F' S' K' A' R' L' H'
        C' Q' N' →
      Cont H C bridge →
        Cont bridge L audit →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist => hsame row audit)
              (fun row : BHist =>
                hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
                  hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
                    hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row audit)
              (fun _row : BHist =>
                Cont H C bridge ∧ Cont bridge L audit ∧ PkgSig bundle N pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier bridgeRoute auditRoute pkgSig
  obtain
    ⟨_sameP, _sameF, _sameS, _sameK, _sameA, _sameR, _sameL, _sameH, _sameC,
      _sameQ, _sameN⟩ := classifier
  exact {
    core := {
      carrier_inhabited := Exists.intro audit (hsame_refl audit)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr source))))))))))
    ledger_sound := by
      intro _row _source
      exact ⟨bridgeRoute, auditRoute, pkgSig⟩
  }

end BEDC.Derived.ReflectiveInquiryUp
