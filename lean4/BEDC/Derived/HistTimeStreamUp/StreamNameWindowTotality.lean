import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_streamname_window_totality [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamWindow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay streamWindow ->
        Cont provenance name publicRead ->
          PkgSig bundle streamWindow pkg ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                    (fun row : BHist =>
                      HistTimeStreamCarrier source schedule start replay transport provenance name
                        bundle pkg ∧ hsame row streamWindow)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        (hsame row source ∨ hsame row schedule ∨ hsame row start ∨
                          hsame row replay ∨ hsame row transport ∨ hsame row provenance ∨
                            hsame row name ∨ hsame row streamWindow))
                    (fun _row : BHist =>
                      Cont source replay streamWindow ∧ Cont provenance name publicRead ∧
                        PkgSig bundle streamWindow pkg ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                UnaryHistory streamWindow ∧ UnaryHistory publicRead ∧
                  Cont source replay streamWindow ∧ Cont provenance name publicRead ∧
                    PkgSig bundle streamWindow pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert UnaryHistory hsame Cont
  intro carrier sourceReplayWindow provenanceNamePublic windowPkg publicPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have windowUnary : UnaryHistory streamWindow :=
    unary_cont_closed sourceUnary replayUnary sourceReplayWindow
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNamePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row streamWindow)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row source ∨ hsame row schedule ∨ hsame row start ∨
                hsame row replay ∨ hsame row transport ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row streamWindow))
          (fun _row : BHist =>
            Cont source replay streamWindow ∧ Cont provenance name publicRead ∧
              PkgSig bundle streamWindow pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro streamWindow ⟨carrierWitness, hsame_refl streamWindow⟩
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
          intro _row _other same sourceRow
          exact ⟨sourceRow.left, hsame_trans (hsame_symm same) sourceRow.right⟩
      }
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport windowUnary (hsame_symm sourceRow.right)
        exact
          ⟨rowUnary,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right))))))⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sourceReplayWindow, provenanceNamePublic, windowPkg, publicPkg⟩
    }
  exact
    ⟨cert, windowUnary, publicUnary, sourceReplayWindow, provenanceNamePublic, windowPkg,
      publicPkg⟩

end BEDC.Derived.HistTimeStreamUp
