import BEDC.Derived.ReflectiveInquiryUp.Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ReflectiveInquiryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReflectiveInquiryNameCertObligationSurface [AskSetup] [PackageSetup]
    {P F S K A R L H C Q N bridge audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReflectiveInquiryCarrier P F S K A R L H C Q N bundle pkg →
      Cont H C bridge →
        Cont bridge L audit →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist => hsame row audit ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
                  hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
                    hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row audit)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont H C bridge ∧ Cont bridge L audit ∧
                  PkgSig bundle N pkg)
              hsame ∧ UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier bridgeRoute auditRoute pkgN
  obtain ⟨_unaryP, _unaryF, _unaryS, _unaryK, _unaryA, _unaryR, unaryL, unaryH,
    unaryC, _unaryQ, _unaryN, _routePF, _routeSK, _routeRL, _routeHC, _pkgN⟩ :=
    carrier
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed unaryH unaryC bridgeRoute
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed bridgeUnary unaryL auditRoute
  have sourceAudit :
      (fun row : BHist => hsame row audit ∧ UnaryHistory row) audit := by
    exact ⟨hsame_refl audit, auditUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row audit ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row P ∨ hsame row F ∨ hsame row S ∨ hsame row K ∨
            hsame row A ∨ hsame row R ∨ hsame row L ∨ hsame row H ∨
              hsame row C ∨ hsame row Q ∨ hsame row N ∨ hsame row audit)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont H C bridge ∧ Cont bridge L audit ∧
            PkgSig bundle N pkg)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
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
      exact ⟨source.right, bridgeRoute, auditRoute, pkgN⟩
  }
  exact ⟨cert, auditUnary⟩

end BEDC.Derived.ReflectiveInquiryUp
