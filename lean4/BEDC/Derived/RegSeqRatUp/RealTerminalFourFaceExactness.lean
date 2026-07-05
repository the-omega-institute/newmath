import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatStreamCarrier_real_terminal_four_face_exactness [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace
      realFace : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            PkgSig bundle realFace pkg ->
              UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧
                UnaryHistory radius ∧ UnaryHistory regularity ∧ UnaryHistory provenance ∧
                  UnaryHistory readback ∧ UnaryHistory streamFace ∧
                    UnaryHistory dyadicFace ∧ UnaryHistory realFace ∧
                      hsame endpoint streamFace ∧ hsame regularity dyadicFace ∧
                        hsame readback realFace ∧ Cont schedule index streamFace ∧
                          Cont endpoint radius dyadicFace ∧ Cont regularity provenance realFace ∧
                            PkgSig bundle readback pkg ∧ PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
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
  exact
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
      provenanceUnary, readbackUnary, streamUnary, dyadicUnary, realUnary,
      endpointSameStream, regularitySameDyadic, readbackSameReal, streamRoute,
      dyadicRoute, realRoute, readbackPkg, realPkg⟩

theorem RegSeqRatRealTerminalFourFaceExactness [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace
      realFace : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            PkgSig bundle realFace pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace)
                  (fun row : BHist => hsame row realFace ∧ PkgSig bundle realFace pkg)
                  hsame ∧
                UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧ UnaryHistory realFace := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier streamRoute dyadicRoute realRoute realPkg
  obtain ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
    provenanceUnary, _readbackUnary, _carrierStreamRoute, _carrierDyadicRoute,
    _carrierRealRoute, _readbackPkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary indexUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed endpointUnary radiusUnary dyadicRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regularityUnary provenanceUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realFace ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace)
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realPkg⟩
  }
  exact ⟨cert, streamUnary, dyadicUnary, realUnary⟩

theorem RegSeqRatFourFaceTerminalPullback [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace realFace
      terminalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            Cont realFace readback terminalRead ->
              PkgSig bundle realFace pkg ->
                PkgSig bundle terminalRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace ∨
                          hsame row terminalRead)
                      (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                      hsame ∧
                    hsame endpoint streamFace ∧ hsame regularity dyadicFace ∧
                      hsame readback realFace ∧ UnaryHistory streamFace ∧
                        UnaryHistory dyadicFace ∧ UnaryHistory realFace ∧
                          UnaryHistory terminalRead ∧ PkgSig bundle readback pkg ∧
                            PkgSig bundle realFace pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute terminalRoute realPkg terminalPkg
  have exactness :=
    RegSeqRatStreamCarrier_real_terminal_four_face_exactness carrier streamRoute dyadicRoute
      realRoute realPkg
  have _scheduleUnary : UnaryHistory schedule := exactness.left
  have _indexUnary : UnaryHistory index := exactness.right.left
  have _endpointUnary : UnaryHistory endpoint := exactness.right.right.left
  have _radiusUnary : UnaryHistory radius := exactness.right.right.right.left
  have _regularityUnary : UnaryHistory regularity := exactness.right.right.right.right.left
  have _provenanceUnary : UnaryHistory provenance := exactness.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback := exactness.right.right.right.right.right.right.left
  have streamUnary : UnaryHistory streamFace :=
    exactness.right.right.right.right.right.right.right.left
  have dyadicUnary : UnaryHistory dyadicFace :=
    exactness.right.right.right.right.right.right.right.right.left
  have realUnary : UnaryHistory realFace :=
    exactness.right.right.right.right.right.right.right.right.right.left
  have endpointSameStream : hsame endpoint streamFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.left
  have regularitySameDyadic : hsame regularity dyadicFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.left
  have readbackSameReal : hsame readback realFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.left
  have _exactStreamRoute : Cont schedule index streamFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have _exactDyadicRoute : Cont endpoint radius dyadicFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have _exactRealRoute : Cont regularity provenance realFace :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have readbackPkg : PkgSig bundle readback pkg :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have exactRealPkg : PkgSig bundle realFace pkg :=
    exactness.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary readbackUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace ∨
              hsame row terminalRead)
          (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact ⟨source.left, terminalPkg⟩
  }
  exact
    ⟨cert, endpointSameStream, regularitySameDyadic, readbackSameReal, streamUnary,
      dyadicUnary, realUnary, terminalUnary, readbackPkg, exactRealPkg, terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
