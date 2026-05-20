import BEDC.Derived.RegSeqRatUp
import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.RegSeqRatUp

theorem StreamNameCommonRefinementTerminalRealSeal [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {window : ProbeBundle BHist}
    {packageBundle : ProbeBundle ProbeName}
    {schedule index endpoint radius regularity provenance readback realSeal terminal : BHist}
    {pkg : Pkg} :
    RatStreamNameCarrier s ->
      RatStreamNameCarrier t ->
        RatStreamNameFiniteWindowClassifier s t window ->
          RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
              packageBundle pkg ->
            UnaryHistory realSeal ->
              Cont readback realSeal terminal ->
                PkgSig packageBundle terminal pkg ->
                UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                  RatStreamNameFiniteWindowClassifier s t window ∧
                    Cont readback realSeal terminal ∧ PkgSig packageBundle readback pkg ∧
                      PkgSig packageBundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig UnaryHistory
  intro _carrierS _carrierT windowClassifier regseqCarrier realSealUnary sealRoute terminalPkg
  obtain
    ⟨_scheduleUnary, _indexUnary, _endpointUnary, _radiusUnary, _regularityUnary,
      _provenanceUnary, readbackUnary, _scheduleRoute, _regularityRoute, _readbackRoute,
      readbackPkg⟩ := regseqCarrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary sealRoute
  exact
    ⟨readbackUnary, realSealUnary, terminalUnary, windowClassifier, sealRoute, readbackPkg,
      terminalPkg⟩

theorem StreamName_common_refinement_terminal_real_seal [AskSetup] [PackageSetup]
    {s t : BHist -> BHist} {bundle : ProbeBundle BHist}
    {packageBundle : ProbeBundle ProbeName} {n window terminal provenance : BHist} {pkg : Pkg} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      InBundle n bundle ->
        UnaryHistory n ->
          UnaryHistory window ->
            UnaryHistory terminal ->
              hsame window (s n) ->
                Cont window terminal provenance ->
                  PkgSig packageBundle provenance pkg ->
                    RatHistoryClassifier (s n) (t n) ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row window ∨ hsame row terminal ∨ hsame row provenance)
                        (fun row : BHist =>
                          hsame row provenance ∧ PkgSig packageBundle provenance pkg)
                        hsame ∧
                      UnaryHistory provenance ∧ PkgSig packageBundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Pkg Cont hsame SemanticNameCert
  intro classifier member nUnary windowUnary terminalUnary _sameWindow provenanceRoute
    provenancePkg
  have selected : RatHistoryClassifier (s n) (t n) :=
    classifier n member nUnary
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed windowUnary terminalUnary provenanceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row terminal ∨ hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ PkgSig packageBundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance
        ⟨hsame_refl provenance, provenanceUnary⟩
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
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨selected, cert, provenanceUnary, provenancePkg⟩

end BEDC.Derived.StreamNameUp
