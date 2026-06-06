import BEDC.Derived.ClosedTermSubstitutionCompilerUp.BridgeRoute

namespace BEDC.Derived.ClosedTermSubstitutionCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ClosedTermSubstitutionCompilerPacket_mature_route [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert operationRead witnessRead compilerRead publicRead binderRead openRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont closedBoundary operation operationRead ->
        Cont operationRead fixedWitness witnessRead ->
          Cont witnessRead nameCert compilerRead ->
            Cont continuation nameCert publicRead ->
              Cont closedBoundary fixedWitness binderRead ->
                Cont binderRead operation openRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle nameCert pkg ->
                      PkgSig bundle publicRead pkg ->
                        PkgSig bundle openRead pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row compilerRead ∧
                                  Cont witnessRead nameCert compilerRead)
                              (fun row : BHist =>
                                hsame row compilerRead ∧
                                  Cont closedBoundary operation operationRead ∧
                                    Cont operationRead fixedWitness witnessRead)
                              (fun row : BHist =>
                                hsame row compilerRead ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle nameCert pkg)
                              hsame ∧
                            SemanticNameCert
                              (fun row : BHist =>
                                hsame row publicRead ∧
                                  ∃ packet : ClosedTermSubstitutionCompilerUp,
                                    packet =
                                      ClosedTermSubstitutionCompilerUp.mk termGenerator
                                        closedBoundary operation fixedWitness transport
                                        continuation provenance nameCert)
                              (fun row : BHist =>
                                hsame row publicRead ∧ Cont continuation nameCert publicRead)
                              (fun row : BHist =>
                                hsame row publicRead ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle publicRead pkg)
                              hsame ∧
                              hsame openRead
                                (append (append closedBoundary fixedWitness) operation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packetWitness boundaryOperation operationWitness witnessCompiler continuationPublic
    binderRoute openRoute provenancePkg namePkg publicPkg openPkg
  have compilerCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row compilerRead ∧ Cont witnessRead nameCert compilerRead)
        (fun row : BHist =>
          hsame row compilerRead ∧ Cont closedBoundary operation operationRead ∧
            Cont operationRead fixedWitness witnessRead)
        (fun row : BHist =>
          hsame row compilerRead ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameCert pkg)
        hsame :=
    ClosedTermSubstitutionCompilerPacket_bridge_route packetWitness boundaryOperation
      operationWitness witnessCompiler provenancePkg namePkg
  have publicCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row publicRead ∧
            ∃ packet : ClosedTermSubstitutionCompilerUp,
              packet =
                ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
                  fixedWitness transport continuation provenance nameCert)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont continuation nameCert publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle publicRead pkg)
        hsame :=
    (ClosedTermSubstitutionCompilerPacket_public_nonescape packetWitness continuationPublic
      provenancePkg publicPkg).left
  have openExact :
      hsame openRead (append (append closedBoundary fixedWitness) operation) :=
    (ClosedTermSubstitutionCompilerPacket_binder_budget_nonescape packetWitness binderRoute
      openRoute provenancePkg openPkg).left
  exact ⟨compilerCert, publicCert, openExact⟩

end BEDC.Derived.ClosedTermSubstitutionCompilerUp
