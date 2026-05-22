import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatTailBudgetTerminalRealSeal [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback streamFace dyadicFace realFace
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
      Cont schedule index streamFace ->
        Cont endpoint radius dyadicFace ->
          Cont regularity provenance realFace ->
            Cont realFace readback terminalRead ->
              PkgSig bundle terminalRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace ∨
                        hsame row terminalRead)
                    (fun row : BHist =>
                      hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                    hsame ∧
                  UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                    UnaryHistory realFace ∧ UnaryHistory terminalRead ∧
                      Cont schedule index streamFace ∧ Cont endpoint radius dyadicFace ∧
                        Cont regularity provenance realFace ∧
                          Cont realFace readback terminalRead ∧ PkgSig bundle readback pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier scheduleIndexStream endpointRadiusDyadic regularityProvenanceReal
    realReadbackTerminal terminalPkg
  obtain ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary,
    provenanceUnary, readbackUnary, _scheduleIndexEndpoint, _endpointRadiusRegularity,
    _regularityProvenanceReadback, readbackPkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed scheduleUnary indexUnary scheduleIndexStream
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed endpointUnary radiusUnary endpointRadiusDyadic
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regularityUnary provenanceUnary regularityProvenanceReal
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary readbackUnary realReadbackTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row) terminalRead := by
    exact ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row streamFace ∨ hsame row dyadicFace ∨ hsame row realFace ∨
            hsame row terminalRead)
        (fun row : BHist => hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminalRead sourceTerminal
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
    ⟨cert, streamUnary, dyadicUnary, realUnary, terminalUnary, scheduleIndexStream,
      endpointRadiusDyadic, regularityProvenanceReal, realReadbackTerminal, readbackPkg,
      terminalPkg⟩

end BEDC.Derived.RegSeqRatUp
