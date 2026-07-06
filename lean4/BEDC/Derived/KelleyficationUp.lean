import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KelleyficationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KelleyficationCarrier [AskSetup] [PackageSetup]
    (topology coreCompact compactOpen window transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory topology ∧ UnaryHistory coreCompact ∧ UnaryHistory compactOpen ∧
    UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont topology coreCompact compactOpen ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem KelleyficationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {topology coreCompact compactOpen window transport replay provenance localName reflected
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KelleyficationCarrier topology coreCompact compactOpen window transport replay provenance
        localName bundle pkg →
      Cont compactOpen window reflected →
        Cont reflected replay exported →
          PkgSig bundle exported pkg →
            UnaryHistory topology ∧ UnaryHistory coreCompact ∧ UnaryHistory compactOpen ∧
              UnaryHistory window ∧ UnaryHistory reflected ∧ UnaryHistory exported ∧
                Cont topology coreCompact compactOpen ∧ Cont compactOpen window reflected ∧
                  Cont reflected replay exported ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exported pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier reflectedRoute exportedRoute exportedPkg
  obtain ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, compactOpenRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed compactOpenUnary windowUnary reflectedRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed reflectedUnary replayUnary exportedRoute
  exact
    ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, reflectedUnary,
      exportedUnary, compactOpenRoute, reflectedRoute, exportedRoute, provenancePkg,
      exportedPkg, localNamePkg⟩

theorem KelleyficationCarrier_public_export_route [AskSetup] [PackageSetup]
    {topology coreCompact compactOpen window transport replay provenance localName reflected
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KelleyficationCarrier topology coreCompact compactOpen window transport replay provenance
        localName bundle pkg →
      Cont compactOpen window reflected →
        Cont reflected replay exported →
          PkgSig bundle exported pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exported ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
                    hsame row window ∨ hsame row reflected ∨ hsame row exported)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
                    Cont compactOpen window reflected ∧ Cont reflected replay exported ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg ∧
                        PkgSig bundle localName pkg)
                hsame ∧
              UnaryHistory exported := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier reflectedRoute exportedRoute exportedPkg
  have obligations :=
    KelleyficationCarrier_namecert_obligations
      (topology := topology) (coreCompact := coreCompact) (compactOpen := compactOpen)
      (window := window) (transport := transport) (replay := replay)
      (provenance := provenance) (localName := localName) (reflected := reflected)
      (exported := exported) (bundle := bundle) (pkg := pkg)
      carrier reflectedRoute exportedRoute exportedPkg
  obtain ⟨_topologyUnary, _coreCompactUnary, _compactOpenUnary, _windowUnary,
    _reflectedUnary, exportedUnary, compactOpenRoute, reflectedRouteFromObligation,
    exportedRouteFromObligation, provenancePkg, exportedPkgFromObligation,
    localNamePkg⟩ := obligations
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
              hsame row window ∨ hsame row reflected ∨ hsame row exported)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
              Cont compactOpen window reflected ∧ Cont reflected replay exported ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactOpenRoute, reflectedRouteFromObligation,
          exportedRouteFromObligation, provenancePkg, exportedPkgFromObligation,
          localNamePkg⟩
  }
  exact ⟨cert, exportedUnary⟩

theorem KelleyficationCarrier_compact_generated_obligation [AskSetup] [PackageSetup]
    {topology coreCompact compactOpen window transport replay provenance localName compactRead
      reflectedOpen : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KelleyficationCarrier topology coreCompact compactOpen window transport replay provenance
        localName bundle pkg →
      Cont coreCompact compactOpen compactRead →
        Cont compactRead window reflectedOpen →
          SemanticNameCert
              (fun row : BHist => hsame row reflectedOpen ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
                  hsame row window ∨ hsame row reflectedOpen)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
                  Cont coreCompact compactOpen compactRead ∧
                    Cont compactRead window reflectedOpen ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory compactRead ∧ UnaryHistory reflectedOpen := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier compactReadRoute reflectedOpenRoute
  obtain ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, compactOpenRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed coreCompactUnary compactOpenUnary compactReadRoute
  have reflectedOpenUnary : UnaryHistory reflectedOpen :=
    unary_cont_closed compactReadUnary windowUnary reflectedOpenRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reflectedOpen ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
              hsame row window ∨ hsame row reflectedOpen)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
              Cont coreCompact compactOpen compactRead ∧
                Cont compactRead window reflectedOpen ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro reflectedOpen ⟨hsame_refl reflectedOpen, reflectedOpenUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactOpenRoute, compactReadRoute, reflectedOpenRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, compactReadUnary, reflectedOpenUnary⟩

-- staging: until CompactlyGeneratedWeakHausdorffUp or CompactOpenExponentialLawUp
-- receives a Lean-side carrier, this theorem records the compact-window replay
-- certificate consumed by those paper neighbours. Expected next steps: add the
-- consumer carrier and route its Kelleyfication row through this certificate.
theorem KelleyficationCarrier_compact_window_exhaustion [AskSetup] [PackageSetup]
    {topology coreCompact compactOpen window transport replay provenance localName compactRead
      reflectedOpen replayedOpen : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KelleyficationCarrier topology coreCompact compactOpen window transport replay provenance
        localName bundle pkg →
      Cont coreCompact compactOpen compactRead →
        Cont compactRead window reflectedOpen →
          Cont reflectedOpen replay replayedOpen →
            PkgSig bundle replayedOpen pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row replayedOpen ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
                      hsame row window ∨ hsame row reflectedOpen ∨ hsame row replayedOpen)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
                      Cont coreCompact compactOpen compactRead ∧
                        Cont compactRead window reflectedOpen ∧
                          Cont reflectedOpen replay replayedOpen ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory reflectedOpen ∧
                  UnaryHistory replayedOpen := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier compactReadRoute reflectedOpenRoute replayedOpenRoute replayedOpenPkg
  obtain ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, compactOpenRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed coreCompactUnary compactOpenUnary compactReadRoute
  have reflectedOpenUnary : UnaryHistory reflectedOpen :=
    unary_cont_closed compactReadUnary windowUnary reflectedOpenRoute
  have replayedOpenUnary : UnaryHistory replayedOpen :=
    unary_cont_closed reflectedOpenUnary replayUnary replayedOpenRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayedOpen ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row topology ∨ hsame row coreCompact ∨ hsame row compactOpen ∨
              hsame row window ∨ hsame row reflectedOpen ∨ hsame row replayedOpen)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont topology coreCompact compactOpen ∧
              Cont coreCompact compactOpen compactRead ∧
                Cont compactRead window reflectedOpen ∧
                  Cont reflectedOpen replay replayedOpen ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayedOpen ⟨hsame_refl replayedOpen, replayedOpenUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactOpenRoute, compactReadRoute, reflectedOpenRoute,
          replayedOpenRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, compactReadUnary, reflectedOpenUnary, replayedOpenUnary⟩

end BEDC.Derived.KelleyficationUp
