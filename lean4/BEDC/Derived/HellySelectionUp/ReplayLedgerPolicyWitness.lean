import BEDC.Derived.HellySelectionUp.NameCertObligations

namespace BEDC.Derived.HellySelectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HellySelection_replay_ledger_policy_witness [AskSetup] [PackageSetup]
    {B A W S R E T C P N selectedRead sealedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont S R selectedRead ->
        Cont selectedRead E sealedRead ->
          Cont sealedRead T replayRead ->
            PkgSig bundle replayRead pkg ->
              (Exists
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg)) ∧
                UnaryHistory selectedRead ∧ UnaryHistory sealedRead ∧
                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier selectedRoute sealedRoute replayRoute replayPkg
  obtain ⟨cert, selectedUnary, sealedUnary, replayUnary⟩ :=
    HellySelection_subsequence_handoff
      (B := B) (A := A) (W := W) (S := S) (R := R) (E := E) (T := T)
      (C := C) (P := P) (N := N) (selectedRead := selectedRead)
      (sealedRead := sealedRead) (replayRead := replayRead) (bundle := bundle)
      (pkg := pkg) carrier selectedRoute sealedRoute replayRoute replayPkg
  have ledgerWitness :
      Exists (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg) :=
    semanticNameCert_ledger_policy_witness cert
  exact ⟨ledgerWitness, selectedUnary, sealedUnary, replayUnary⟩

theorem HellySelection_variation_window_seal_ledger_witness [AskSetup] [PackageSetup]
    {B A W S R E T C P N variationRead boundedRead selectedRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HellySelectionCarrier B A W S R E T C P N bundle pkg ->
      Cont B A variationRead ->
        Cont variationRead W boundedRead ->
          Cont S R selectedRead ->
            Cont selectedRead E sealedRead ->
              PkgSig bundle sealedRead pkg ->
                (Exists
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealedRead pkg)) ∧
                  UnaryHistory boundedRead ∧ UnaryHistory selectedRead ∧
                    UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier variationRoute boundedRoute selectedRoute sealedRoute sealedPkg
  obtain ⟨cert, boundedUnary, selectedUnary, sealedUnary⟩ :=
    HellySelection_finite_variation_window_handoff
      (B := B) (A := A) (W := W) (S := S) (R := R) (E := E) (T := T)
      (C := C) (P := P) (N := N) (variationRead := variationRead)
      (boundedRead := boundedRead) (selectedRead := selectedRead)
      (sealedRead := sealedRead) (bundle := bundle) (pkg := pkg) carrier
      variationRoute boundedRoute selectedRoute sealedRoute sealedPkg
  have ledgerWitness :
      Exists (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealedRead pkg) :=
    semanticNameCert_ledger_policy_witness cert
  exact ⟨ledgerWitness, boundedUnary, selectedUnary, sealedUnary⟩

end BEDC.Derived.HellySelectionUp
