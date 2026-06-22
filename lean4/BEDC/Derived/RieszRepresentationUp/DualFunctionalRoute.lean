import BEDC.Derived.RieszRepresentationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RieszRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RieszRepresentationDualFunctionalRoute [AskSetup] [PackageSetup]
    {source functional bound branch transportedFunctional boundedRead branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory functional ->
        UnaryHistory bound ->
          UnaryHistory branch ->
            Cont source functional transportedFunctional ->
              Cont transportedFunctional bound boundedRead ->
                Cont boundedRead branch branchRead ->
                  PkgSig bundle branchRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row source ∨ hsame row functional ∨ hsame row bound ∨
                            hsame row branch ∨ hsame row transportedFunctional ∨
                              hsame row boundedRead ∨ hsame row branchRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont source functional transportedFunctional ∧
                            Cont transportedFunctional bound boundedRead ∧
                              Cont boundedRead branch branchRead ∧
                                PkgSig bundle branchRead pkg)
                        hsame ∧
                      UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary functionalUnary boundUnary branchUnary sourceFunctional functionalBound
    boundBranch branchPkg
  have transportedFunctionalUnary : UnaryHistory transportedFunctional :=
    unary_cont_closed sourceUnary functionalUnary sourceFunctional
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed transportedFunctionalUnary boundUnary functionalBound
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed boundedReadUnary branchUnary boundBranch
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row functional ∨ hsame row bound ∨ hsame row branch ∨
              hsame row transportedFunctional ∨ hsame row boundedRead ∨ hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source functional transportedFunctional ∧
              Cont transportedFunctional bound boundedRead ∧ Cont boundedRead branch branchRead ∧
                PkgSig bundle branchRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead ⟨hsame_refl branchRead, branchReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceFunctional, functionalBound, boundBranch, branchPkg⟩
  }
  exact ⟨cert, branchReadUnary⟩

end BEDC.Derived.RieszRepresentationUp
