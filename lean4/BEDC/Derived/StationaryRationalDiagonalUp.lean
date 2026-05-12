import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

/-!
# StationaryRationalDiagonalUp finite carrier surface.
-/

namespace BEDC.Derived.StationaryRationalDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def StationaryRationalDiagonalCarrier [AskSetup] [PackageSetup]
    (rat constantStream regseq diagonal realSeal transport route provenance namecert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory rat ∧ UnaryHistory constantStream ∧ UnaryHistory regseq ∧
    UnaryHistory diagonal ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory namecert ∧
        UnaryHistory endpoint ∧ Cont rat constantStream regseq ∧
          Cont regseq diagonal realSeal ∧ Cont realSeal transport route ∧
            Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row namecert)
                (fun row : BHist => hsame row namecert)
                (fun row : BHist => hsame row namecert)
                hsame

theorem StationaryRationalDiagonalCarrier_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {rat constantStream regseq diagonal realSeal transport route provenance namecert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal transport
        route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row realSeal)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row realSeal)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row realSeal)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal (And.intro carrier (hsame_refl realSeal))
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem StationaryRationalDiagonalCarrier_real_handoff [AskSetup] [PackageSetup]
    {rat constantStream regseq diagonal realSeal transport route provenance namecert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal transport
        route provenance namecert endpoint bundle pkg →
      UnaryHistory rat ∧
        UnaryHistory constantStream ∧
          UnaryHistory regseq ∧
            UnaryHistory diagonal ∧
              UnaryHistory realSeal ∧
                Cont rat constantStream regseq ∧
                  Cont regseq diagonal realSeal ∧
                    Cont realSeal transport route ∧
                      Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨ratUnary, constantStreamUnary, regseqUnary, diagonalUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary,
    constantStreamRoute, diagonalSealRoute, transportRoute, provenanceEndpoint, pkgSig,
    _nameCert⟩ := carrier
  exact And.intro ratUnary
    (And.intro constantStreamUnary
      (And.intro regseqUnary
        (And.intro diagonalUnary
          (And.intro realSealUnary
            (And.intro constantStreamRoute
              (And.intro diagonalSealRoute
                (And.intro transportRoute
                  (And.intro provenanceEndpoint pkgSig))))))))

theorem StationaryRationalDiagonalCarrier_constant_window_totality
    [AskSetup] [PackageSetup]
    {rat constantStream regseq diagonal realSeal transport route provenance namecert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal transport
        route provenance namecert endpoint bundle pkg ->
      UnaryHistory rat ∧ UnaryHistory constantStream ∧ UnaryHistory regseq ∧
        hsame regseq (append rat constantStream) ∧ hsame realSeal (append regseq diagonal) ∧
          PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨ratUnary, constantStreamUnary, regseqUnary, _diagonalUnary, _realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _namecertUnary, _endpointUnary,
    constantStreamRoute, diagonalSealRoute, _transportRoute, _provenanceEndpoint, pkgSig,
    _nameCert⟩ := carrier
  exact And.intro ratUnary
    (And.intro constantStreamUnary
      (And.intro regseqUnary
        (And.intro constantStreamRoute
          (And.intro diagonalSealRoute pkgSig))))

theorem StationaryRationalDiagonalCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {rat constantStream regseq diagonal realSeal transport route provenance namecert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal transport
        route provenance namecert endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          StationaryRationalDiagonalCarrier rat constantStream regseq diagonal realSeal
              transport route provenance namecert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.StationaryRationalDiagonalUp
