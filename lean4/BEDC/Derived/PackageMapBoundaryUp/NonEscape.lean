import BEDC.Derived.PackageMapBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PackageMapBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PackageMapBoundaryNonEscape [AskSetup] [PackageSetup]
    {T G R S X A H C P N auditRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    packageMapBoundaryFields (PackageMapBoundaryUp.mk T G R S X A H C P N) =
        [T, G, R, S, X, A, H, C, P, N] →
      Cont A C auditRead →
        Cont auditRead N nameRead →
          PkgSig bundle nameRead pkg →
            UnaryHistory A →
              UnaryHistory C →
                UnaryHistory N →
                  SemanticNameCert
                      (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row G ∨ hsame row R ∨ hsame row S ∨
                          hsame row X ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row auditRead ∨
                              hsame row nameRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont A C auditRead ∧
                          Cont auditRead N nameRead ∧ PkgSig bundle nameRead pkg)
                      hsame ∧ UnaryHistory auditRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldsExact auditRoute nameRoute namePkg unaryA unaryC unaryN
  cases fieldsExact
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryA unaryC auditRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed auditUnary unaryN nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row G ∨ hsame row R ∨ hsame row S ∨
              hsame row X ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row auditRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A C auditRead ∧
              Cont auditRead N nameRead ∧ PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRoute, nameRoute, namePkg⟩
  }
  exact ⟨cert, auditUnary, nameUnary⟩

end BEDC.Derived.PackageMapBoundaryUp
