import BEDC.Derived.CompactNetModulusSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactNetModulusSelectorCarrier [AskSetup] [PackageSetup]
    (source target tolerance probes centers radii moduli fold precision transport route
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory tolerance ∧
    UnaryHistory probes ∧ UnaryHistory centers ∧ UnaryHistory radii ∧
      UnaryHistory moduli ∧ UnaryHistory fold ∧ UnaryHistory precision ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
          UnaryHistory localName ∧ Cont source probes centers ∧
            Cont moduli fold precision ∧ Cont precision route localName ∧
              PkgSig bundle provenance pkg

theorem CompactNetModulusSelectorNameCertObligations [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead modulusRead precisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg →
      Cont source probes compactRead →
        Cont moduli fold modulusRead →
          Cont precision route precisionRead →
            PkgSig bundle precisionRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    CompactNetModulusSelectorCarrier source target tolerance probes centers
                        radii moduli fold precision transport route provenance localName
                        bundle pkg ∧
                      hsame row precision)
                  (fun row : BHist =>
                    Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
                      Cont precision route precisionRead ∧ hsame row precision)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle precisionRead pkg ∧
                      hsame row precision)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory precisionRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier sourceProbesCompact moduliFoldModulus precisionRouteRead precisionReadPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have sourceAtPrecision :
      (fun row : BHist =>
        CompactNetModulusSelectorCarrier source target tolerance probes centers radii
            moduli fold precision transport route provenance localName bundle pkg ∧
          hsame row precision) precision := by
    exact ⟨carrierWitness, hsame_refl precision⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CompactNetModulusSelectorCarrier source target tolerance probes centers radii
                moduli fold precision transport route provenance localName bundle pkg ∧
              hsame row precision)
          (fun row : BHist =>
            Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
              Cont precision route precisionRead ∧ hsame row precision)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle precisionRead pkg ∧
              hsame row precision)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro precision sourceAtPrecision
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨sourceProbesCompact, moduliFoldModulus, precisionRouteRead, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, precisionReadPkg, source.right⟩
  }
  exact ⟨cert, compactReadUnary, modulusReadUnary, precisionReadUnary⟩

theorem CompactNetModulusSelectorCarrier_nonescape [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead modulusRead precisionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead ->
        Cont moduli fold modulusRead ->
          Cont precision route precisionRead ->
            Cont precisionRead localName publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactRead ∨ hsame row modulusRead ∨
                        hsame row precisionRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                        hsame row publicRead)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory precisionRead ∧ UnaryHistory publicRead ∧
                      Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
                        Cont precision route precisionRead ∧
                          Cont precisionRead localName publicRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier sourceProbesCompact moduliFoldModulus precisionRouteRead
    precisionLocalPublic publicReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed precisionReadUnary localNameUnary precisionLocalPublic
  have sourcePublicRead :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactRead ∨ hsame row modulusRead ∨
              hsame row precisionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublicRead
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
      exact ⟨provenancePkg, publicReadPkg, source.left⟩
  }
  exact
    ⟨cert, compactReadUnary, modulusReadUnary, precisionReadUnary, publicReadUnary,
      sourceProbesCompact, moduliFoldModulus, precisionRouteRead, precisionLocalPublic,
      provenancePkg, publicReadPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
