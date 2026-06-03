import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactCompactWindowRootAdmission [AskSetup] [PackageSetup]
    {X x r B K A H C P N compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B K compactRead ->
      PkgSig bundle P pkg ->
        UnaryHistory B ->
          UnaryHistory K ->
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
                    hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      Cont B K compactRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont B K compactRead ∧ PkgSig bundle P pkg)
                hsame ∧ UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro compactRoute provenancePkg closedBallUnary compactWitnessUnary
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed closedBallUnary compactWitnessUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                Cont B K compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B K compactRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactReadUnary⟩
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
      intro _row _source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr compactRoute)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, provenancePkg⟩
  }
  exact ⟨cert, compactReadUnary⟩

end BEDC.Derived.LocallyCompactUp
