import BEDC.Derived.StableManifoldUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StableManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StableManifoldLocalAttraction [AskSetup] [PackageSetup]
    {equilibrium flowRow odeRow chartRow contractionRow tangentRow transportRow replayRow
      provenance localName sourceEndpoint nextEndpoint ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableManifoldCarrier equilibrium flowRow odeRow chartRow contractionRow tangentRow
        transportRow replayRow provenance localName bundle pkg ->
      UnaryHistory sourceEndpoint ->
        Cont tangentRow sourceEndpoint ledgerRead ->
          Cont ledgerRead contractionRow nextEndpoint ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle localName pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row nextEndpoint ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row equilibrium ∨ hsame row tangentRow ∨ hsame row contractionRow ∨
                      hsame row ledgerRead ∨ hsame row nextEndpoint)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory nextEndpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceUnary ledgerRoute contractionRoute provenancePkg localNamePkg
  obtain ⟨_equilibriumUnary, _flowUnary, _odeUnary, _chartUnary, contractionUnary,
    tangentUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed tangentUnary sourceUnary ledgerRoute
  have nextUnary : UnaryHistory nextEndpoint :=
    unary_cont_closed ledgerUnary contractionUnary contractionRoute
  have endpointSource :
      (fun row : BHist => hsame row nextEndpoint ∧ UnaryHistory row) nextEndpoint := by
    exact ⟨hsame_refl nextEndpoint, nextUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row nextEndpoint ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row equilibrium ∨ hsame row tangentRow ∨ hsame row contractionRow ∨
            hsame row ledgerRead ∨ hsame row nextEndpoint)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro nextEndpoint endpointSource
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
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.1,
            unary_transport source.2 same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.1)))
    ledger_sound := by
      intro _row source
      exact ⟨source.2, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, ledgerUnary, nextUnary⟩

end BEDC.Derived.StableManifoldUp
