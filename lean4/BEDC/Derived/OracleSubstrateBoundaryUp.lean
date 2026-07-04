import BEDC.Derived.OracleSubstrateBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OracleSubstrateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OracleSubstrateBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {substrate query external refusal localRow transport replay provenance nameCert queryBoundary
      refusalRoute publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory substrate ->
      UnaryHistory query ->
        UnaryHistory external ->
          UnaryHistory refusal ->
            UnaryHistory localRow ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont substrate query queryBoundary ->
                    Cont query external refusalRoute ->
                      Cont refusal replay provenance ->
                        PkgSig bundle provenance pkg ->
                          hsame provenance publicRead ->
                            hsame publicRead nameCert ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row substrate ∨ hsame row query ∨
                                      hsame row external ∨ hsame row refusal ∨
                                        hsame row localRow ∨ hsame row queryBoundary ∨
                                          hsame row refusalRoute ∨ hsame row provenance ∨
                                            hsame row nameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont substrate query queryBoundary ∧
                                        Cont query external refusalRoute ∧
                                          Cont refusal replay provenance ∧
                                            PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory queryBoundary ∧ UnaryHistory refusalRoute ∧
                                  UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro substrateUnary queryUnary externalUnary refusalUnary _localUnary _transportUnary
    replayUnary substrateQuery queryExternal refusalReplay provenancePkg provenancePublic
    publicName
  have queryBoundaryUnary : UnaryHistory queryBoundary :=
    unary_cont_closed substrateUnary queryUnary substrateQuery
  have refusalRouteUnary : UnaryHistory refusalRoute :=
    unary_cont_closed queryUnary externalUnary queryExternal
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed refusalUnary replayUnary refusalReplay
  have publicReadUnary : UnaryHistory publicRead :=
    unary_transport provenanceUnary provenancePublic
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport publicReadUnary publicName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row substrate ∨ hsame row query ∨ hsame row external ∨
              hsame row refusal ∨ hsame row localRow ∨ hsame row queryBoundary ∨
                hsame row refusalRoute ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont substrate query queryBoundary ∧
              Cont query external refusalRoute ∧ Cont refusal replay provenance ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      left
      exact hsame_trans source.left (hsame_symm provenancePublic)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, substrateQuery, queryExternal, refusalReplay, provenancePkg⟩
  }
  exact ⟨cert, queryBoundaryUnary, refusalRouteUnary, nameCertUnary⟩

theorem OracleSubstrateBoundaryCarrier_external_channel_nonescape
    (O : OracleSubstrateBoundaryUp) :
    ∃ S Q E R L H C P N : BHist,
      oracleSubstrateBoundaryFields O = [S, Q, E, R, L, H, C, P, N] ∧
        hsame Q Q ∧ hsame E E ∧ hsame R R ∧ Cont Q E (append Q E) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases O with
  | mk S Q E R L H C P N =>
      exact
        ⟨S, Q, E, R, L, H, C, P, N, rfl, hsame_refl Q, hsame_refl E,
          hsame_refl R, rfl⟩

theorem OracleSubstrateBoundary_external_channel_nonescape [AskSetup] [PackageSetup]
    {substrate query external refusal localRow transport replay provenance nameCert queryBoundary
      refusalRoute publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory substrate ->
      UnaryHistory query ->
        UnaryHistory external ->
          UnaryHistory refusal ->
            UnaryHistory localRow ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont substrate query queryBoundary ->
                    Cont query external refusalRoute ->
                      Cont refusal replay provenance ->
                        PkgSig bundle provenance pkg ->
                          hsame provenance publicRead ->
                            hsame publicRead nameCert ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row substrate ∨ hsame row query ∨
                                      hsame row external ∨ hsame row refusal ∨
                                        hsame row localRow ∨ hsame row queryBoundary ∨
                                          hsame row refusalRoute ∨ hsame row provenance ∨
                                            hsame row nameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont substrate query queryBoundary ∧
                                        Cont query external refusalRoute ∧
                                          Cont refusal replay provenance ∧
                                            PkgSig bundle provenance pkg)
                                  hsame ∧
                                UnaryHistory queryBoundary ∧ UnaryHistory refusalRoute ∧
                                  UnaryHistory publicRead ∧ UnaryHistory nameCert ∧
                                    hsame provenance nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro substrateUnary queryUnary externalUnary refusalUnary localUnary transportUnary
    replayUnary substrateQuery queryExternal refusalReplay provenancePkg provenancePublic
    publicName
  have obligations :=
    OracleSubstrateBoundaryCarrier_namecert_obligations (substrate := substrate)
      (query := query) (external := external) (refusal := refusal)
      (localRow := localRow) (transport := transport) (replay := replay)
      (provenance := provenance) (nameCert := nameCert) (queryBoundary := queryBoundary)
      (refusalRoute := refusalRoute) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) substrateUnary queryUnary externalUnary refusalUnary localUnary
      transportUnary replayUnary substrateQuery queryExternal refusalReplay provenancePkg
      provenancePublic publicName
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed refusalUnary replayUnary refusalReplay
  have publicReadUnary : UnaryHistory publicRead :=
    unary_transport provenanceUnary provenancePublic
  have provenanceName : hsame provenance nameCert :=
    hsame_trans provenancePublic publicName
  exact
    ⟨obligations.left, obligations.right.left, obligations.right.right.left,
      publicReadUnary, obligations.right.right.right, provenanceName⟩

end BEDC.Derived.OracleSubstrateBoundaryUp
