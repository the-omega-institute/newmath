import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamnameWindowReindexDeterminacy [AskSetup] [PackageSetup]
    {window0 window1 endpoint support route publicSection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window0 →
      UnaryHistory window1 →
        UnaryHistory route →
          hsame window0 window1 →
            hsame endpoint endpoint →
              Cont window0 route publicSection →
                Cont window1 route publicSection →
                  PkgSig bundle support pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicSection ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row window0 ∨ hsame row window1 ∨ hsame row endpoint ∨
                            hsame row support ∨ hsame row publicSection)
                        (fun row : BHist =>
                          UnaryHistory row ∧ hsame window0 window1 ∧
                            Cont window0 route publicSection ∧
                              Cont window1 route publicSection ∧ PkgSig bundle support pkg)
                        hsame ∧
                      UnaryHistory publicSection := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro window0Unary _window1Unary routeUnary windowsSame endpointSame route0 route1 supportPkg
  have publicUnary : UnaryHistory publicSection :=
    unary_cont_closed window0Unary routeUnary route0
  have sourcePublic :
      (fun row : BHist => hsame row publicSection ∧ UnaryHistory row) publicSection := by
    exact ⟨hsame_refl publicSection, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicSection ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window0 ∨ hsame row window1 ∨ hsame row endpoint ∨ hsame row support ∨
              hsame row publicSection)
          (fun row : BHist =>
            UnaryHistory row ∧ hsame window0 window1 ∧ Cont window0 route publicSection ∧
              Cont window1 route publicSection ∧ PkgSig bundle support pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicSection sourcePublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowsSame, route0, route1, supportPkg⟩
  }
  cases endpointSame
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.StreamNameUp
