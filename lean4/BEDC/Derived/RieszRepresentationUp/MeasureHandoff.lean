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

theorem RieszRepresentationMeasureHandoff [AskSetup] [PackageSetup]
    {source target functional representing ledger boundary measureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory target ->
        UnaryHistory functional ->
          UnaryHistory representing ->
            UnaryHistory boundary ->
              Cont functional representing ledger ->
                Cont ledger boundary measureRead ->
                  PkgSig bundle measureRead pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row measureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                        (fun row : BHist =>
                          hsame row source ∨ hsame row target ∨ hsame row functional ∨
                            hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                              hsame row measureRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont functional representing ledger ∧
                            Cont ledger boundary measureRead ∧ PkgSig bundle measureRead pkg)
                        hsame ∧
                      UnaryHistory ledger ∧ UnaryHistory measureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary targetUnary functionalUnary representingUnary boundaryUnary
    functionalRepresenting ledgerBoundary measurePkg
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed functionalUnary representingUnary functionalRepresenting
  have measureUnary : UnaryHistory measureRead :=
    unary_cont_closed ledgerUnary boundaryUnary ledgerBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row measureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row functional ∨
              hsame row representing ∨ hsame row ledger ∨ hsame row boundary ∨
                hsame row measureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont functional representing ledger ∧
              Cont ledger boundary measureRead ∧ PkgSig bundle measureRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro measureRead ⟨hsame_refl measureRead, measureUnary, measurePkg⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right.left, functionalRepresenting, ledgerBoundary, measurePkg⟩
  }
  exact ⟨cert, ledgerUnary, measureUnary⟩

end BEDC.Derived.RieszRepresentationUp
