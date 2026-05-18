import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWitnessedRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWitnessedRefutationCarrier [AskSetup] [PackageSetup]
    (regularity gap key witness decision transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regularity ∧ UnaryHistory gap ∧ UnaryHistory witness ∧
    UnaryHistory route ∧ Cont regularity gap key ∧ Cont key witness decision ∧
      Cont decision route transport ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem FiniteWitnessedRefutationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg ->
      Cont decision route publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                FiniteWitnessedRefutationCarrier regularity gap key witness decision transport
                    route provenance name bundle pkg ∧ hsame row decision)
              (fun row : BHist => hsame row decision ∧ UnaryHistory publicRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                  hsame row decision)
              hsame ∧
            UnaryHistory key ∧ UnaryHistory decision ∧ UnaryHistory publicRead ∧
              Cont regularity gap key ∧ Cont key witness decision ∧
                Cont decision route publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier decisionRoutePublic publicPkg
  have carrierWitness :
      FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg := carrier
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
              provenance name bundle pkg ∧ hsame row decision)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro decision
        (And.intro carrierWitness (hsame_refl decision))
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
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
                provenance name bundle pkg ∧ hsame row decision)
          (fun row : BHist => hsame row decision ∧ UnaryHistory publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row decision)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row source
        exact And.intro source.right publicUnary
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg (And.intro publicPkg source.right)
    }
  exact
    And.intro semantic
      (And.intro keyUnary
        (And.intro decisionUnary
          (And.intro publicUnary
            (And.intro regularityGapKey
              (And.intro keyWitnessDecision
                (And.intro decisionRoutePublic
                  (And.intro provenancePkg (And.intro namePkg publicPkg))))))))

end BEDC.Derived.FiniteWitnessedRefutationUp
