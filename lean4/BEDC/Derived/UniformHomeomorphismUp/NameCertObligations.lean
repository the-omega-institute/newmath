import BEDC.Derived.UniformHomeomorphismUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformHomeomorphismCarrier [AskSetup] [PackageSetup]
    (source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory forward ∧
    UnaryHistory inverse ∧ UnaryHistory forwardUC ∧ UnaryHistory inverseUC ∧
      UnaryHistory forwardMod ∧ UnaryHistory inverseMod ∧ UnaryHistory compatibility ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem UniformHomeomorphismNameCertObligations [AskSetup] [PackageSetup]
    {source target forward inverse forwardUC inverseUC forwardMod inverseMod compatibility replay
      provenance localName namedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformHomeomorphismCarrier source target forward inverse forwardUC inverseUC forwardMod
      inverseMod compatibility replay provenance localName bundle pkg →
      Cont forward forwardUC forwardMod →
        Cont inverse inverseUC inverseMod →
          Cont forwardMod inverseMod compatibility →
            Cont compatibility replay namedRoute →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row forwardMod ∨ hsame row inverseMod ∨
                        hsame row compatibility ∨ hsame row namedRoute)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont forward forwardUC forwardMod ∧
                        Cont inverse inverseUC inverseMod ∧
                          Cont forwardMod inverseMod compatibility ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory namedRoute := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier forwardRoute inverseRoute compatibilityRoute namedRouteReplay localNamePkg
  obtain ⟨_sourceUnary, _targetUnary, forwardUnary, inverseUnary, forwardUCUnary,
    inverseUCUnary, _forwardModUnary, _inverseModUnary, _compatibilityUnary, replayUnary,
    _provenanceUnary, _localNameUnary, provenancePkg, _carrierLocalNamePkg⟩ := carrier
  have forwardModUnary : UnaryHistory forwardMod :=
    unary_cont_closed forwardUnary forwardUCUnary forwardRoute
  have inverseModUnary : UnaryHistory inverseMod :=
    unary_cont_closed inverseUnary inverseUCUnary inverseRoute
  have compatibilityUnary : UnaryHistory compatibility :=
    unary_cont_closed forwardModUnary inverseModUnary compatibilityRoute
  have namedRouteUnary : UnaryHistory namedRoute :=
    unary_cont_closed compatibilityUnary replayUnary namedRouteReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row forwardMod ∨ hsame row inverseMod ∨ hsame row compatibility ∨
              hsame row namedRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont forward forwardUC forwardMod ∧
              Cont inverse inverseUC inverseMod ∧ Cont forwardMod inverseMod compatibility ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRoute ⟨hsame_refl namedRoute, namedRouteUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, forwardRoute, inverseRoute, compatibilityRoute, provenancePkg,
            localNamePkg⟩
    }
  exact ⟨cert, namedRouteUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
