import BEDC.Derived.ClosedTermSubstitutionCompilerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ClosedTermSubstitutionCompilerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ClosedTermSubstitutionCompilerPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    (termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert : BHist)
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (route : Cont continuation nameCert nameCert)
    (provenancePkg : PkgSig bundle provenance pkg)
    (namePkg : PkgSig bundle nameCert pkg) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row nameCert ∧
          ∃ packet : ClosedTermSubstitutionCompilerUp,
            packet =
              ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
                fixedWitness transport continuation provenance nameCert)
      (fun row : BHist => hsame row nameCert ∧ Cont continuation nameCert nameCert)
      (fun row : BHist => hsame row nameCert ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle nameCert pkg)
      hsame := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  constructor
  · constructor
    · exact
        Exists.intro nameCert
          ⟨hsame_refl nameCert,
            Exists.intro
              (ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
                fixedWitness transport continuation provenance nameCert) rfl⟩
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' same source
      exact
        ⟨hsame_trans (hsame_symm same) source.left,
          source.right⟩
  · intro _row source
    exact ⟨source.left, route⟩
  · intro _row source
    exact ⟨source.left, provenancePkg, namePkg⟩

theorem ClosedTermSubstitutionCompilerPacket_self_compile_route [AskSetup] [PackageSetup]
    (termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert operationRead : BHist)
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (boundaryOperation : Cont closedBoundary operation operationRead)
    (operationWitness : Cont operationRead fixedWitness nameCert)
    (provenancePkg : PkgSig bundle provenance pkg)
    (namePkg : PkgSig bundle nameCert pkg) :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ∧
      hsame nameCert (append (append closedBoundary operation) fixedWitness) ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  have selfRoute :
      hsame nameCert (append (append closedBoundary operation) fixedWitness) :=
    operationWitness.trans (congrArg (fun row => append row fixedWitness) boundaryOperation)
  exact
    ⟨Exists.intro
        (ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
          transport continuation provenance nameCert)
        rfl,
      selfRoute, provenancePkg, namePkg⟩

end BEDC.Derived.ClosedTermSubstitutionCompilerUp
