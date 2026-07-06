import BEDC.Derived.StreamNameUp.OpenPhaseFourFaceExitReadback

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameOpenPhaseLeanRouteTotality [AskSetup] [PackageSetup]
    {stream dyadic regseq real support exit terminal readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont regseq real exit ->
                Cont support exit terminal ->
                  Cont terminal support readback ->
                    PkgSig bundle terminal pkg ->
                      PkgSig bundle readback pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row stream ∨ hsame row dyadic ∨ hsame row regseq ∨
                                hsame row real ∨ hsame row terminal ∨ hsame row readback)
                            (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                            hsame ∧
                          UnaryHistory support ∧ UnaryHistory exit ∧ UnaryHistory terminal ∧
                            UnaryHistory readback ∧ hsame terminal (append support exit) ∧
                              hsame readback (append terminal support) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro streamUnary dyadicUnary regseqUnary realUnary streamDyadicSupport regseqRealExit
    supportExitTerminal terminalSupportReadback terminalPkg readbackPkg
  obtain ⟨cert, supportUnary, exitUnary, terminalUnary, readbackUnary, _streamRoute,
    _exitRoute, terminalRoute, readbackRoute, _terminalPkg, _readbackPkg⟩ :=
      StreamNameOpenPhaseFourFaceExitReadback streamUnary dyadicUnary regseqUnary realUnary
        streamDyadicSupport regseqRealExit supportExitTerminal terminalSupportReadback
        terminalPkg readbackPkg
  have terminalReadback : hsame terminal (append support exit) :=
    cont_deterministic terminalRoute (cont_intro rfl)
  have readbackReadback : hsame readback (append terminal support) :=
    cont_deterministic readbackRoute (cont_intro rfl)
  exact
    ⟨cert, supportUnary, exitUnary, terminalUnary, readbackUnary, terminalReadback,
      readbackReadback⟩

end BEDC.Derived.StreamNameUp
