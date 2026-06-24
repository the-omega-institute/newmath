import BEDC.Derived.UniformBoundednessUp.BaireHandoff

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessBaireHandoffCompatibility [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      baireRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg ->
      Cont pointwise baire baireRead ->
        PkgSig bundle baireRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row baireRead)
              (fun row : BHist =>
                hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨
                  hsame row baireRead)
              (fun row : BHist =>
                hsame row baireRead ∧ Cont family pointwise baire ∧
                  Cont pointwise baire baireRead ∧ PkgSig bundle baireRead pkg)
              hsame ∧
            PkgSig bundle history pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro packet pointwiseBaireRead baireReadPkg
  rcases packet with
    ⟨_sameNameHistory, familyPointwiseBaire, _baireNormRegseq, _regseqStreamHistory,
      _transportHistoryReplay, _replayProvenanceNameRow, _packageProvenance,
      packageHistory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row baireRead)
          (fun row : BHist =>
            hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨
              hsame row baireRead)
          (fun row : BHist =>
            hsame row baireRead ∧ Cont family pointwise baire ∧
              Cont pointwise baire baireRead ∧ PkgSig bundle baireRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro baireRead (hsame_refl baireRead)
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
      exact Or.inr (Or.inr (Or.inr source))
    ledger_sound := by
      intro _row source
      exact ⟨source, familyPointwiseBaire, pointwiseBaireRead, baireReadPkg⟩
  }
  exact ⟨cert, packageHistory⟩

end BEDC.Derived.UniformBoundednessUp
