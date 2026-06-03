import BEDC.Derived.RealMetricUp
import BEDC.Derived.RealMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X Y A D S R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricCarrier X Y A D S R H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row A ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory A ∧ UnaryHistory D ∧
          UnaryHistory S ∧ UnaryHistory R ∧ PkgSig bundle P pkg ∧
            PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier
  have xUnary : UnaryHistory X := carrier.left
  have yUnary : UnaryHistory Y := carrier.right.left
  have aUnary : UnaryHistory A := carrier.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have nPkg : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row A ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro N
          ⟨hsame_refl N,
            carrier.right.right.right.right.right.right.right.right.right.left⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, nPkg⟩
  }
  exact
    ⟨cert, xUnary, yUnary, aUnary, dUnary, sUnary, rUnary, pPkg, nPkg⟩

end BEDC.Derived.RealMetricUp
