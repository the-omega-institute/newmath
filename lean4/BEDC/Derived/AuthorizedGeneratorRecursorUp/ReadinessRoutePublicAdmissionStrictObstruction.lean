import BEDC.Derived.AuthorizedGeneratorRecursorUp.ReadinessRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorReadinessRoutePublicAdmissionStrictObstruction
    [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert generator compiler refusal replay publicRead obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorReadinessRoute signature eliminator motive branch descent output
      audit transport continuation provenance boundary localCert generator compiler refusal replay
      bundle pkg ->
      Cont output refusal obstruction ->
        Cont obstruction localCert publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont output refusal obstruction ∧ Cont obstruction localCert row ∧
                  PkgSig bundle publicRead pkg)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro route outputRefusal obstructionLocal publicPkg
  rcases route with
    ⟨carrier, _signatureGenerator, _generatorOutput, boundaryAuditRefusal,
      _transportReplay, _provenancePkg, _localCertPkg⟩
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, _descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _signatureMotive, _motiveDescent, _descentAudit,
      _transportSame, _provenancePkgFromCarrier⟩
  have refusalUnary : UnaryHistory refusal :=
    unary_cont_closed boundaryUnary auditUnary boundaryAuditRefusal
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed outputUnary refusalUnary outputRefusal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed obstructionUnary localCertUnary obstructionLocal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨outputRefusal, cont_result_hsame_transport obstructionLocal
          (hsame_symm source.left), publicPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
