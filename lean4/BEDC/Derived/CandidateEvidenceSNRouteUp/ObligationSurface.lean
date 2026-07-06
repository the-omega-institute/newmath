import BEDC.Derived.CandidateEvidenceSNRouteUp.NoInfiniteBoundary

namespace BEDC.Derived.CandidateEvidenceSNRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CandidateEvidenceSNRouteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {E K M A I H C P N candidateRead closedRead memberRead adequacyRead noInfiniteRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont E K candidateRead ->
      Cont K M closedRead ->
        Cont M A memberRead ->
          Cont A I adequacyRead ->
            Cont adequacyRead C noInfiniteRead ->
              Cont H C replayRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row noInfiniteRead ∧
                            (Cont E K candidateRead ∧ Cont K M closedRead ∧
                              Cont M A memberRead ∧ Cont A I adequacyRead ∧
                                Cont adequacyRead C noInfiniteRead))
                        (fun row : BHist =>
                          hsame row E ∨ hsame row K ∨ hsame row M ∨ hsame row A ∨
                            hsame row I ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row candidateRead ∨
                                hsame row closedRead ∨ hsame row memberRead ∨
                                  hsame row adequacyRead ∨ hsame row noInfiniteRead)
                        (fun row : BHist =>
                          hsame row noInfiniteRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle N pkg)
                        hsame ∧
                      Cont H C replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro candidateRoute closedRoute memberRoute adequacyRoute noInfiniteRoute replayRoute
    provenancePkg namePkg
  have routeSurface :
      Cont E K candidateRead ∧ Cont K M closedRead ∧ Cont M A memberRead ∧
        Cont A I adequacyRead ∧ Cont adequacyRead C noInfiniteRead :=
    ⟨candidateRoute, closedRoute, memberRoute, adequacyRoute, noInfiniteRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row noInfiniteRead ∧
              (Cont E K candidateRead ∧ Cont K M closedRead ∧
                Cont M A memberRead ∧ Cont A I adequacyRead ∧
                  Cont adequacyRead C noInfiniteRead))
          (fun row : BHist =>
            hsame row E ∨ hsame row K ∨ hsame row M ∨ hsame row A ∨
              hsame row I ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row candidateRead ∨ hsame row closedRead ∨
                  hsame row memberRead ∨ hsame row adequacyRead ∨
                    hsame row noInfiniteRead)
          (fun row : BHist =>
            hsame row noInfiniteRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro noInfiniteRead ⟨hsame_refl noInfiniteRead, routeSurface⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨cert, replayRoute, provenancePkg, namePkg⟩

end BEDC.Derived.CandidateEvidenceSNRouteUp
