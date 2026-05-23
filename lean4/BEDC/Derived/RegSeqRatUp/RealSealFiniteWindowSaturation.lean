import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatStreamCarrier_real_seal_finite_window_saturation [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace
      realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            PkgSig bundle realFace pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row streamFace ∨ hsame row dyadicFace ∨
                      hsame row regularity ∨ hsame row realFace)
                  (fun row : BHist => hsame row realFace ∧ PkgSig bundle realFace pkg)
                  hsame ∧
                UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧ UnaryHistory realFace ∧
                  hsame endpoint streamFace ∧ hsame regularity dyadicFace ∧
                    hsame readback realFace ∧ PkgSig bundle readback pkg ∧
                      PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier streamRoute dyadicRoute realRoute realPkg
  obtain ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
    provenanceUnary, readbackUnary, carrierStreamRoute, carrierDyadicRoute, carrierRealRoute,
    readbackPkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary indexUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed endpointUnary radiusUnary dyadicRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regularityUnary provenanceUnary realRoute
  have endpointSameStream : hsame endpoint streamFace :=
    cont_deterministic carrierStreamRoute streamRoute
  have regularitySameDyadic : hsame regularity dyadicFace :=
    cont_deterministic carrierDyadicRoute dyadicRoute
  have readbackSameReal : hsame readback realFace :=
    cont_deterministic carrierRealRoute realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamFace ∨ hsame row dyadicFace ∨
              hsame row regularity ∨ hsame row realFace)
          (fun row : BHist => hsame row realFace ∧ PkgSig bundle realFace pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realFace
        ⟨hsame_refl realFace, realUnary⟩
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
      exact ⟨source.left, realPkg⟩
  }
  exact
    ⟨cert, streamUnary, dyadicUnary, realUnary, endpointSameStream, regularitySameDyadic,
      readbackSameReal, readbackPkg, realPkg⟩

end BEDC.Derived.RegSeqRatUp
