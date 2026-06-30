import BEDC.Derived.BanachSpaceUp.CompletionObligationSurface
import BEDC.Derived.BanachSpaceUp.LinearCompletionNonescape
import BEDC.Derived.BanachSpaceUp.SeparatedNameCertObligation

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceObligationUpgradeScope [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L completionRead namedRead cauchyWindow completionWindow
      terminalSeal separatedRead completionWindow2 terminalWindow separatedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg) ->
      Cont Q S completionRead ->
        Cont completionRead E namedRead ->
          PkgSig bundle namedRead pkg ->
            Cont Q S cauchyWindow ->
              Cont cauchyWindow R completionWindow ->
                Cont completionWindow E terminalSeal ->
                  Cont terminalSeal Z separatedRead ->
                    Cont Q S completionWindow2 ->
                      Cont completionWindow2 R terminalWindow ->
                        Cont terminalWindow Z separatedWindow ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row V ∨ hsame row N ∨ hsame row M ∨
                                  hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                    hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row L ∨
                                        hsame row completionRead ∨ hsame row namedRead)
                              (fun row : BHist => PkgSig bundle row pkg)
                              hsame ∧
                            UnaryHistory cauchyWindow ∧
                              UnaryHistory completionWindow ∧
                                UnaryHistory terminalSeal ∧
                                  UnaryHistory separatedRead ∧
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row separatedWindow ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                            hsame row E ∨ hsame row Z ∨ hsame row L ∨
                                              hsame row completionWindow2 ∨
                                                hsame row terminalWindow ∨
                                                  hsame row separatedWindow)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont Q S completionWindow2 ∧
                                              Cont completionWindow2 R terminalWindow ∧
                                                Cont terminalWindow Z separatedWindow ∧
                                                  hsame row separatedWindow)
                                        hsame ∧
                                      banachSpaceFields
                                          (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                        [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert UnaryHistory
  intro packet completionRoute namedRoute namedPkg cauchyRoute completionRoute2
    terminalRoute separatedRoute completionRoute3 terminalRoute2 separatedRoute2
  have packetInput := packet
  obtain ⟨_vUnary, _nUnary, _mUnary, qUnary, sUnary, rUnary, eUnary, zUnary,
    _hUnary, _cUnary, _pUnary, lUnary, _pkgP⟩ := packet
  have completionSurface :=
    BanachSpaceCompletionObligationSurface
      (V := V) (N := N) (M := M) (Q := Q) (S := S) (R := R) (E := E)
      (Z := Z) (H := H) (C := C) (P := P) (L := L)
      (completionRead := completionRead) (namedRead := namedRead)
      (bundle := bundle) (pkg := pkg) packetInput completionRoute namedRoute namedPkg
  have nonescape :=
    BanachSpaceLinearCompletionNonescape
      (V := V) (N := N) (M := M) (Q := Q) (S := S) (R := R) (E := E)
      (Z := Z) (H := H) (C := C) (P := P) (L := L)
      (cauchyWindow := cauchyWindow) (completionWindow := completionWindow)
      (terminalSeal := terminalSeal) (separatedRead := separatedRead)
      qUnary sUnary rUnary eUnary zUnary cauchyRoute completionRoute2 terminalRoute
      separatedRoute
  obtain ⟨cauchyUnary, completionUnary, terminalUnary, separatedUnary, _fields⟩ :=
    nonescape
  have separatedCert :=
    BanachSpaceCarrier_separated_namecert_obligation
      (V := V) (N := N) (M := M) (Q := Q) (S := S) (R := R) (E := E)
      (Z := Z) (H := H) (C := C) (P := P) (L := L)
      (completionWindow := completionWindow2) (terminalWindow := terminalWindow)
      (separatedWindow := separatedWindow)
      qUnary sUnary rUnary eUnary zUnary lUnary completionRoute3 terminalRoute2
      separatedRoute2
  obtain ⟨separatedNameCert, _separatedWindowUnary, separatedFields⟩ := separatedCert
  exact
    ⟨completionSurface, cauchyUnary, completionUnary, terminalUnary, separatedUnary,
      separatedNameCert, separatedFields⟩

end BEDC.Derived.BanachSpaceUp
