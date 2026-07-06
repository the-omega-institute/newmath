import BEDC.Derived.HeineCantorModulusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.HeineCantorModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem HeineCantorModulusCarrier_finite_net_extraction [AskSetup] [PackageSetup]
    {source target map precision net centers radii modulus triangle transport replay provenance
      name extracted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont net centers extracted →
      PkgSig bundle extracted pkg →
        SemanticNameCert
          (fun row : BHist =>
            hsame row extracted ∧
              ∃ packet : HeineCantorModulusUp,
                packet =
                  HeineCantorModulusUp.mk source target map precision net centers radii
                    modulus triangle transport replay provenance name)
          (fun row : BHist => hsame row net ∨ hsame row centers ∨ hsame row extracted)
          (fun row : BHist =>
            hsame row extracted ∧ Cont net centers extracted ∧ PkgSig bundle extracted pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro extractedCont extractedPkg
  let packet :=
    HeineCantorModulusUp.mk source target map precision net centers radii modulus triangle
      transport replay provenance name
  have sourceExtracted :
      (fun row : BHist =>
        hsame row extracted ∧
          ∃ packet : HeineCantorModulusUp,
            packet =
              HeineCantorModulusUp.mk source target map precision net centers radii modulus
                triangle transport replay provenance name) extracted := by
    exact ⟨hsame_refl extracted, Exists.intro packet rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro extracted sourceExtracted
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact ⟨hsame_trans (hsame_symm same) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, extractedCont, extractedPkg⟩
  }

theorem HeineCantorModulusCarrier_triangle_handoff [AskSetup] [PackageSetup]
    {source target map precision net centers radii modulus triangle transport replay provenance
      name extracted uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont net centers extracted →
      Cont radii modulus triangle →
        Cont extracted triangle uniformRead →
          PkgSig bundle uniformRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row uniformRead ∧
                  ∃ packet : HeineCantorModulusUp,
                    packet =
                      HeineCantorModulusUp.mk source target map precision net centers radii
                        modulus triangle transport replay provenance name)
              (fun row : BHist =>
                hsame row net ∨ hsame row centers ∨ hsame row radii ∨ hsame row modulus ∨
                  hsame row triangle ∨ hsame row uniformRead)
              (fun row : BHist =>
                hsame row uniformRead ∧ Cont net centers extracted ∧
                  Cont radii modulus triangle ∧ Cont extracted triangle uniformRead ∧
                    PkgSig bundle uniformRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro finiteNetRoute triangleRoute uniformReadRoute uniformPkg
  let packet :=
    HeineCantorModulusUp.mk source target map precision net centers radii modulus triangle
      transport replay provenance name
  have sourceUniformRead :
      (fun row : BHist =>
        hsame row uniformRead ∧
          ∃ packet : HeineCantorModulusUp,
            packet =
              HeineCantorModulusUp.mk source target map precision net centers radii modulus
                triangle transport replay provenance name) uniformRead := by
    exact ⟨hsame_refl uniformRead, Exists.intro packet rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniformRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact ⟨hsame_trans (hsame_symm same) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, finiteNetRoute, triangleRoute, uniformReadRoute, uniformPkg⟩
  }

end BEDC.Derived.HeineCantorModulusUp
