import BEDC.Derived.SubstitutionAuditMapUp.Core

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubstitutionAuditMapCarrier_formal_target_package [AskSetup] [PackageSetup]
    {term closed shift substitute composition generator transport route provenance name
      replayRead namedRead ledgerRead publicRead downstreamRead formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionAuditMapCarrier term closed shift substitute composition generator transport route
        provenance name bundle pkg ->
      Cont transport route replayRead ->
        Cont replayRead name namedRead ->
          Cont provenance name ledgerRead ->
            Cont namedRead ledgerRead publicRead ->
              Cont route name downstreamRead ->
                Cont publicRead downstreamRead formalRead ->
                  PkgSig bundle namedRead pkg ->
                    PkgSig bundle ledgerRead pkg ->
                      PkgSig bundle publicRead pkg ->
                        PkgSig bundle downstreamRead pkg ->
                          PkgSig bundle formalRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row publicRead ∨ hsame row downstreamRead ∨
                                    hsame row formalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle formalRead pkg)
                                hsame ∧
                              UnaryHistory publicRead ∧ UnaryHistory downstreamRead ∧
                                UnaryHistory formalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro carrier replayRoute namedRoute ledgerRoute publicRoute downstreamRoute formalRoute
    _namedPkg _ledgerPkg _publicPkg _downstreamPkg formalPkg
  obtain ⟨_termUnary, _closedUnary, _shiftUnary, _substituteUnary, _compositionUnary,
    _generatorUnary, transportUnary, routeUnary, provenanceUnary, nameUnary, _termClosed,
    _shiftSubstitute, _compositionGenerator, _transportRoute, _provenanceName,
    _nameGenerator, _provenancePkg, _namePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary routeUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nameUnary namedRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed provenanceUnary nameUnary ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary ledgerUnary publicRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed routeUnary nameUnary downstreamRoute
  have formalUnary : UnaryHistory formalRead :=
    unary_cont_closed publicUnary downstreamUnary formalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row downstreamRead ∨ hsame row formalRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle formalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro formalRead
        ⟨hsame_refl formalRead, formalUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, formalPkg⟩
  }
  exact ⟨cert, publicUnary, downstreamUnary, formalUnary⟩

end BEDC.Derived.SubstitutionAuditMapUp
