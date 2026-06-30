import BEDC.Derived.ReflectiveInquiryUp.Carrier

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectiveInquiryObligationClosurePackage [AskSetup] [PackageSetup]
    {P F S K A R L H C Q N P' F' S' K' A' R' L' H' C' Q' N'
      bridge audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectiveInquiryCarrier P F S K A R L H C Q N bundle pkg →
      ReflectiveInquiryClassifier P F S K A R L H C Q N P' F' S' K' A' R' L' H'
        C' Q' N' →
        Cont H C bridge →
          Cont bridge L audit →
            PkgSig bundle audit pkg →
              SemanticNameCert
                (fun row : BHist => hsame row audit ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
                    hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
                      hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row audit)
                (fun row : BHist =>
                  hsame row audit ∧ Cont H C bridge ∧ Cont bridge L audit ∧
                    PkgSig bundle audit pkg)
                hsame ∧ UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier classifier bridgeRoute auditRoute auditPkg
  obtain ⟨_unaryP, _unaryF, _unaryS, _unaryK, _unaryA, _unaryR, unaryL, unaryH,
    unaryC, _unaryQ, _unaryN, _routePF, _routeSK, _routeRL, _routeHC, _pkgN⟩ :=
    carrier
  obtain ⟨_sameP, _sameF, _sameS, _sameK, _sameA, _sameR, _sameL, _sameH,
    _sameC, _sameQ, _sameN⟩ := classifier
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed unaryH unaryC bridgeRoute
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed bridgeUnary unaryL auditRoute
  have sourceAudit :
      (fun row : BHist => hsame row audit ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        audit := by
    exact ⟨hsame_refl audit, auditUnary, auditPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row audit ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
            hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
              hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row audit)
        (fun row : BHist =>
          hsame row audit ∧ Cont H C bridge ∧ Cont bridge L audit ∧
            PkgSig bundle audit pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro audit sourceAudit
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
        intro row other sameRows source
        cases source.left
        cases sameRows
        exact source
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
                        (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgeRoute, auditRoute, auditPkg⟩
  }
  exact ⟨cert, auditUnary⟩

end BEDC.Derived.ReflectiveInquiryUp
