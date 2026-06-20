import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedSearchRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedSearchRefutationCarrier [AskSetup] [PackageSetup]
    (proposition budget frontier refutation gap transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory proposition ∧ UnaryHistory budget ∧ UnaryHistory frontier ∧
    UnaryHistory refutation ∧ UnaryHistory gap ∧ UnaryHistory replay ∧
      Cont proposition budget frontier ∧ Cont frontier refutation transport ∧
        Cont transport replay gap ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg

theorem BoundedSearchRefutationNameCertObligations [AskSetup] [PackageSetup]
    {proposition budget frontier refutation gap transport replay provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport replay
        provenance name bundle pkg ->
      Cont frontier refutation publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                BoundedSearchRefutationCarrier proposition budget frontier refutation gap
                    transport replay provenance name bundle pkg ∧ hsame row frontier)
              (fun row : BHist =>
                hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
                  hsame row refutation ∨ hsame row gap ∨ hsame row publicRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                  hsame row frontier)
              hsame ∧ UnaryHistory frontier ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier frontierRefutationPublic publicPkg
  have carrierWitness :
      BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport
        replay provenance name bundle pkg := carrier
  obtain ⟨propositionUnary, budgetUnary, frontierUnary, refutationUnary, _gapUnary,
    _replayUnary, _propositionBudgetFrontier, _frontierRefutationTransport,
    _transportReplayGap, provenancePkg, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed frontierUnary refutationUnary frontierRefutationPublic
  have certCore :
      NameCert
        (fun row : BHist =>
          BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport
              replay provenance name bundle pkg ∧ hsame row frontier)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro frontier
        (And.intro carrierWitness (hsame_refl frontier))
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
            BoundedSearchRefutationCarrier proposition budget frontier refutation gap
                transport replay provenance name bundle pkg ∧ hsame row frontier)
          (fun row : BHist =>
            hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
              hsame row refutation ∨ hsame row gap ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row frontier)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inl source.right))
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg (And.intro publicPkg source.right)
    }
  exact And.intro semantic (And.intro frontierUnary publicUnary)

end BEDC.Derived.BoundedSearchRefutationUp
