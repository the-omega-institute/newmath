import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceRecipeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ChoiceRecipeLedgerCarrier [AskSetup] [PackageSetup]
    (request recipes output refusal transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont request recipes output ∧ Cont output refusal route ∧
          Cont route transport provenance ∧ PkgSig bundle localName pkg

theorem ChoiceRecipeLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg →
      Cont provenance localName obligationRead →
        PkgSig bundle obligationRead pkg →
          UnaryHistory request ∧ UnaryHistory recipes ∧ UnaryHistory output ∧
            UnaryHistory refusal ∧ UnaryHistory provenance ∧ UnaryHistory obligationRead ∧
              Cont request recipes output ∧ Cont output refusal route ∧
                Cont route transport provenance ∧ Cont provenance localName obligationRead ∧
                  PkgSig bundle localName pkg ∧ PkgSig bundle obligationRead pkg ∧
                    SemanticNameCert
                      (fun row : BHist =>
                        ChoiceRecipeLedgerCarrier request recipes output refusal transport route
                            provenance localName bundle pkg ∧
                          hsame row obligationRead)
                      (fun row : BHist =>
                        Cont request recipes output ∧ Cont output refusal route ∧
                          Cont route transport provenance ∧
                            Cont provenance localName row ∧ PkgSig bundle obligationRead pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligationRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier provenanceLocalName obligationReadPkg
  obtain ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, transportUnary, routeUnary,
    provenanceUnary, localNameUnary, requestRecipesOutput, outputRefusalRoute,
    routeTransportProvenance, localNamePkg⟩ := carrier
  have carrierWitness :
      ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance
          localName bundle pkg :=
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, transportUnary, routeUnary,
      provenanceUnary, localNameUnary, requestRecipesOutput, outputRefusalRoute,
      routeTransportProvenance, localNamePkg⟩
  have obligationReadUnary : UnaryHistory obligationRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalName
  have nameCert :
      SemanticNameCert
        (fun row : BHist =>
          ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance
              localName bundle pkg ∧
            hsame row obligationRead)
        (fun row : BHist =>
          Cont request recipes output ∧ Cont output refusal route ∧
            Cont route transport provenance ∧
              Cont provenance localName row ∧ PkgSig bundle obligationRead pkg)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle obligationRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead (And.intro carrierWitness (hsame_refl obligationRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨requestRecipesOutput, outputRefusalRoute, routeTransportProvenance,
          cont_result_hsame_transport provenanceLocalName (hsame_symm source.right),
          obligationReadPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport obligationReadUnary (hsame_symm source.right), obligationReadPkg⟩
  }
  exact
    ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, provenanceUnary,
      obligationReadUnary, requestRecipesOutput, outputRefusalRoute, routeTransportProvenance,
      provenanceLocalName, localNamePkg, obligationReadPkg, nameCert⟩

end BEDC.Derived.ChoiceRecipeLedgerUp
