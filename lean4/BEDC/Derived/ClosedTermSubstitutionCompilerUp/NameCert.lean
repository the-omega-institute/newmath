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

theorem ClosedTermSubstitutionCompilerPacket_classifier_transport [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance nameCert
      transportedBoundary transportedWitness transportedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont closedBoundary operation transportedBoundary ->
        Cont transportedBoundary fixedWitness transportedWitness ->
          hsame transportedWitness transportedName ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle transportedName pkg ->
                hsame transportedName nameCert ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row transportedName ∧
                        ∃ packet : ClosedTermSubstitutionCompilerUp,
                          packet =
                            ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary
                              operation fixedWitness transport continuation provenance nameCert)
                    (fun row : BHist =>
                      hsame row nameCert ∧ Cont closedBoundary operation transportedBoundary ∧
                        Cont transportedBoundary fixedWitness transportedWitness)
                    (fun row : BHist =>
                      hsame row transportedName ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle transportedName pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packetWitness boundaryTransport witnessTransport _sameWitnessName provenancePkg
    transportedPkg sameTransportedNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro transportedName
        (And.intro (hsame_refl transportedName) packetWitness)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro row source
      exact
        And.intro (hsame_trans source.left sameTransportedNameCert)
          (And.intro boundaryTransport witnessTransport)
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg transportedPkg)
  }

theorem ClosedTermSubstitutionCompilerPacket_boundary_ledger_exactness [AskSetup]
    [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert operationRead witnessRead ledger audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont closedBoundary operation operationRead ->
        Cont operationRead fixedWitness witnessRead ->
          Cont operationRead witnessRead ledger ->
            Cont ledger nameCert audit ->
              PkgSig bundle provenance pkg ->
                PkgSig bundle nameCert pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row audit ∧
                          ∃ packet : ClosedTermSubstitutionCompilerUp,
                            packet =
                              ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary
                                operation fixedWitness transport continuation provenance nameCert)
                      (fun row : BHist =>
                        Cont operationRead witnessRead ledger ∧ Cont ledger nameCert audit ∧
                          hsame row audit)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
                          hsame row audit)
                      hsame ∧
                    hsame witnessRead (append operationRead fixedWitness) ∧
                      hsame ledger (append operationRead witnessRead) ∧
                        hsame audit (append ledger nameCert) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packetWitness _boundaryOperation operationWitness witnessLedger ledgerName
    provenancePkg namePkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row audit ∧
            ∃ packet : ClosedTermSubstitutionCompilerUp,
              packet =
                ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
                  fixedWitness transport continuation provenance nameCert)
        (fun row : BHist =>
          Cont operationRead witnessRead ledger ∧ Cont ledger nameCert audit ∧
            hsame row audit)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧ hsame row audit)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro audit (And.intro (hsame_refl audit) packetWitness)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro witnessLedger (And.intro ledgerName source.left)
    ledger_sound := by
      intro _row source
      exact And.intro provenancePkg (And.intro namePkg source.left)
  }
  exact
    And.intro cert
      (And.intro operationWitness (And.intro witnessLedger ledgerName))

theorem ClosedTermSubstitutionCompilerPacket_obligation_closure_package [AskSetup]
    [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert operationRead witnessRead ledger audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont closedBoundary operation operationRead ->
        Cont operationRead fixedWitness witnessRead ->
          Cont witnessRead continuation ledger ->
            Cont ledger nameCert audit ->
              PkgSig bundle provenance pkg ->
                PkgSig bundle nameCert pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row audit ∧
                          ∃ packet : ClosedTermSubstitutionCompilerUp,
                            packet =
                              ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary
                                operation fixedWitness transport continuation provenance nameCert)
                      (fun row : BHist =>
                        Cont operationRead fixedWitness witnessRead ∧
                          Cont ledger nameCert audit ∧ hsame row audit)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
                          hsame row audit)
                      hsame ∧
                    hsame witnessRead (append operationRead fixedWitness) ∧
                      hsame audit (append ledger nameCert) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packetWitness _boundaryOperation operationWitness _witnessContinuationLedger ledgerName
    provenancePkg namePkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row audit ∧
            ∃ packet : ClosedTermSubstitutionCompilerUp,
              packet =
                ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
                  fixedWitness transport continuation provenance nameCert)
        (fun row : BHist =>
          Cont operationRead fixedWitness witnessRead ∧ Cont ledger nameCert audit ∧
            hsame row audit)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧ hsame row audit)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro audit (And.intro (hsame_refl audit) packetWitness)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro operationWitness (And.intro ledgerName source.left)
    ledger_sound := by
      intro _row source
      exact And.intro provenancePkg (And.intro namePkg source.left)
  }
  exact And.intro cert (And.intro operationWitness ledgerName)

theorem ClosedTermSubstitutionCompilerPacket_boundary [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert operationRead witnessRead shiftRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont closedBoundary operation operationRead ->
        Cont operationRead fixedWitness witnessRead ->
          Cont closedBoundary fixedWitness shiftRead ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle nameCert pkg ->
                hsame witnessRead (append operationRead fixedWitness) ∧
                  hsame shiftRead (append closedBoundary fixedWitness) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro packetWitness _boundaryOperation operationWitness shiftWitness provenancePkg namePkg
  obtain ⟨_packet, packetEq⟩ := packetWitness
  cases packetEq
  exact ⟨operationWitness, shiftWitness, provenancePkg, namePkg⟩

theorem ClosedTermSubstitutionCompilerPacket_binder_budget_nonescape [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance nameCert
      binderRead openRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) →
      Cont closedBoundary fixedWitness binderRead →
        Cont binderRead operation openRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle openRead pkg →
              hsame openRead (append (append closedBoundary fixedWitness) operation) ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle openRead pkg ∧
                  Cont closedBoundary fixedWitness binderRead ∧
                    Cont binderRead operation openRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packetWitness binderRoute openRoute provenancePkg openPkg
  obtain ⟨_packet, packetEq⟩ := packetWitness
  cases packetEq
  have openExact : hsame openRead (append (append closedBoundary fixedWitness) operation) := by
    cases binderRoute
    exact openRoute
  exact
    ⟨openExact, provenancePkg, openPkg, binderRoute, openRoute⟩

theorem ClosedTermSubstitutionCompilerPacket_public_nonescape [AskSetup] [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance nameCert
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) ->
      Cont continuation nameCert publicRead ->
        PkgSig bundle provenance pkg ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row publicRead ∧
                    ∃ packet : ClosedTermSubstitutionCompilerUp,
                      packet =
                        ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary
                          operation fixedWitness transport continuation provenance nameCert)
                (fun row : BHist =>
                  hsame row publicRead ∧ Cont continuation nameCert publicRead)
                (fun row : BHist =>
                  hsame row publicRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle publicRead pkg)
                hsame ∧
              hsame publicRead (append continuation nameCert) ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packetWitness continuationNamePublic provenancePkg publicPkg
  have cert :
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
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, packetWitness⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, continuationNamePublic⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, continuationNamePublic, provenancePkg, publicPkg⟩

theorem ClosedTermSubstitutionCompilerPacket_shift_substitute_compatibility [AskSetup]
    [PackageSetup]
    {termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert substitutionRead shiftRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ packet : ClosedTermSubstitutionCompilerUp,
        packet =
          ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
            transport continuation provenance nameCert) →
      Cont closedBoundary operation substitutionRead →
        Cont closedBoundary fixedWitness shiftRead →
          Cont substitutionRead shiftRead sharedRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle sharedRead pkg →
                hsame substitutionRead (append closedBoundary operation) ∧
                  hsame shiftRead (append closedBoundary fixedWitness) ∧
                    hsame sharedRead (append substitutionRead shiftRead) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro packetWitness substitutionRoute shiftRoute sharedRoute provenancePkg sharedPkg
  obtain ⟨_packet, packetEq⟩ := packetWitness
  cases packetEq
  exact ⟨substitutionRoute, shiftRoute, sharedRoute, provenancePkg, sharedPkg⟩

end BEDC.Derived.ClosedTermSubstitutionCompilerUp
