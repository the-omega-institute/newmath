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

theorem StreamNameOpenPhaseExitBoundary [AskSetup] [PackageSetup]
    {stream dyadic regseq real support exit terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont regseq real exit ->
                Cont support exit terminal ->
                  PkgSig bundle terminal pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row terminal ∧ Cont support exit terminal)
                        (fun row : BHist => UnaryHistory row ∧ hsame row terminal)
                        (fun row : BHist => PkgSig bundle terminal pkg ∧ hsame row terminal)
                        hsame ∧
                      UnaryHistory support ∧ UnaryHistory exit ∧ UnaryHistory terminal ∧
                        Cont stream dyadic support ∧ Cont regseq real exit ∧
                          Cont support exit terminal ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro streamUnary dyadicUnary regseqUnary realUnary streamDyadicSupport regseqRealExit
    supportExitTerminal terminalPkg
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSupport
  have exitUnary : UnaryHistory exit :=
    unary_cont_closed regseqUnary realUnary regseqRealExit
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed supportUnary exitUnary supportExitTerminal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ Cont support exit terminal)
        (fun row : BHist => UnaryHistory row ∧ hsame row terminal)
        (fun row : BHist => PkgSig bundle terminal pkg ∧ hsame row terminal)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal
        ⟨hsame_refl terminal, supportExitTerminal⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨unary_transport terminalUnary (hsame_symm source.left), source.left⟩
    ledger_sound := by
      intro row source
      exact ⟨terminalPkg, source.left⟩
  }
  exact
    ⟨cert, supportUnary, exitUnary, terminalUnary, streamDyadicSupport, regseqRealExit,
      supportExitTerminal, terminalPkg⟩

theorem StreamNameOpenPhaseFourObjectSufficiency [AskSetup] [PackageSetup]
    {streamWindow dyadicLedger regseqRead realSeal support exitRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory streamWindow ->
      UnaryHistory dyadicLedger ->
        UnaryHistory regseqRead ->
          UnaryHistory realSeal ->
            Cont streamWindow dyadicLedger support ->
              Cont regseqRead realSeal exitRead ->
                Cont support exitRead terminal ->
                  PkgSig bundle terminal pkg ->
                    UnaryHistory support ∧ UnaryHistory exitRead ∧ UnaryHistory terminal ∧
                      Cont streamWindow dyadicLedger support ∧
                        Cont regseqRead realSeal exitRead ∧ Cont support exitRead terminal ∧
                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro streamUnary dyadicUnary regseqUnary realUnary streamDyadicSupport regseqRealExit
    supportExitTerminal terminalPkg
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSupport
  have exitReadUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realUnary regseqRealExit
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed supportUnary exitReadUnary supportExitTerminal
  exact
    ⟨supportUnary, exitReadUnary, terminalUnary, streamDyadicSupport, regseqRealExit,
      supportExitTerminal, terminalPkg⟩

end BEDC.Derived.StreamNameUp
