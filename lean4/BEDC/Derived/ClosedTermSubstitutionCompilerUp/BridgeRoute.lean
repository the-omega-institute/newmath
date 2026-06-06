import BEDC.Derived.ClosedTermSubstitutionCompilerUp.NameCert

namespace BEDC.Derived.ClosedTermSubstitutionCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ClosedTermSubstitutionCompilerPacket_bridge_route [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance nameCert
      operationRead witnessRead compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) →
      Cont closedBoundary operation operationRead →
        Cont operationRead fixedWitness witnessRead →
          Cont witnessRead nameCert compilerRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle nameCert pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row compilerRead ∧ Cont witnessRead nameCert compilerRead)
                  (fun row : BHist =>
                    hsame row compilerRead ∧ Cont closedBoundary operation operationRead ∧
                      Cont operationRead fixedWitness witnessRead)
                  (fun row : BHist =>
                    hsame row compilerRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle nameCert pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _packetWitness boundaryOperation operationWitness witnessCompiler provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compilerRead
          (And.intro (hsame_refl compilerRead) witnessCompiler)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left (And.intro boundaryOperation operationWitness)
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

end BEDC.Derived.ClosedTermSubstitutionCompilerUp
