import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MonotoneCauchyConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MonotoneCauchyConvergenceCarrier [AskSetup] [PackageSetup]
    (S R O B D L E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧
    UnaryHistory R ∧
      UnaryHistory O ∧
        UnaryHistory B ∧
          UnaryHistory D ∧
            UnaryHistory L ∧
              UnaryHistory E ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧
                    UnaryHistory P ∧
                      UnaryHistory N ∧
                        Cont S R D ∧
                          Cont D L E ∧
                            PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg

private def MonotoneCauchyConvergenceSource
    (S R O B D L E N : BHist) (row : BHist) : Prop :=
  hsame row S ∨
    hsame row R ∨
      hsame row O ∨
        hsame row B ∨
          hsame row D ∨
            hsame row L ∨
              hsame row E ∨
                hsame row N

private theorem MonotoneCauchyConvergenceNameCertObligations_unary
    {S R O B D L E N row : BHist}
    (uS : UnaryHistory S) (uR : UnaryHistory R) (uO : UnaryHistory O)
    (uB : UnaryHistory B) (uD : UnaryHistory D) (uL : UnaryHistory L)
    (uE : UnaryHistory E) (uN : UnaryHistory N) :
    MonotoneCauchyConvergenceSource S R O B D L E N row → UnaryHistory row := by
  -- BEDC touchpoint anchor: BHist hsame
  intro source
  cases source with
  | inl sameS =>
      exact unary_transport uS (hsame_symm sameS)
  | inr rest =>
      cases rest with
      | inl sameR =>
          exact unary_transport uR (hsame_symm sameR)
      | inr rest =>
          cases rest with
          | inl sameO =>
              exact unary_transport uO (hsame_symm sameO)
          | inr rest =>
              cases rest with
              | inl sameB =>
                  exact unary_transport uB (hsame_symm sameB)
              | inr rest =>
                  cases rest with
                  | inl sameD =>
                      exact unary_transport uD (hsame_symm sameD)
                  | inr rest =>
                      cases rest with
                      | inl sameL =>
                          exact unary_transport uL (hsame_symm sameL)
                      | inr rest =>
                          cases rest with
                          | inl sameE =>
                              exact unary_transport uE (hsame_symm sameE)
                          | inr sameN =>
                              exact unary_transport uN (hsame_symm sameN)

private theorem MonotoneCauchyConvergenceNameCertObligations_ledger
    [AskSetup] [PackageSetup]
    {S R O B D L E N P row : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (pkgP : PkgSig bundle P pkg) :
    MonotoneCauchyConvergenceSource S R O B D L E N row →
      PkgSig bundle P pkg ∨ PkgSig bundle row pkg := by
  -- BEDC touchpoint anchor: BHist Pkg
  intro _source
  exact Or.inl pkgP

theorem MonotoneCauchyConvergenceNameCertObligations [AskSetup] [PackageSetup]
    {S R O B D L E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyConvergenceCarrier S R O B D L E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row S ∨
              hsame row R ∨
                hsame row O ∨
                  hsame row B ∨
                    hsame row D ∨
                      hsame row L ∨
                        hsame row E ∨
                          hsame row N)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle P pkg ∨ PkgSig bundle row pkg)
          hsame ∧
        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist NameCert SemanticNameCert Pkg
  intro carrier
  rcases carrier with
    ⟨uS, uR, uO, uB, uD, uL, uE, _uH, _uC, _uP, uN, _routeSRD, _routeDLE,
      pkgP, _pkgN⟩
  have sourceUnary :
      ∀ {row : BHist},
        MonotoneCauchyConvergenceSource S R O B D L E N row → UnaryHistory row :=
    MonotoneCauchyConvergenceNameCertObligations_unary uS uR uO uB uD uL uE uN
  have sourceLedger :
      ∀ {row : BHist},
        MonotoneCauchyConvergenceSource S R O B D L E N row →
          PkgSig bundle P pkg ∨ PkgSig bundle row pkg :=
    MonotoneCauchyConvergenceNameCertObligations_ledger (P := P) pkgP
  constructor
  · exact
      { core :=
          { carrier_inhabited := ⟨S, Or.inl (hsame_refl S)⟩
            equiv_refl := by
              intro _row _source
              exact hsame_refl _row
            equiv_symm := by
              intro _row _row' sameRows
              exact hsame_symm sameRows
            equiv_trans := by
              intro _row _row' _row'' sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro row row' sameRows sourceRow
              cases sourceRow with
              | inl sameS =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameS)
              | inr rest =>
                  cases rest with
                  | inl sameR =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR))
                  | inr rest =>
                      cases rest with
                      | inl sameO =>
                          exact Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameO)))
                      | inr rest =>
                          cases rest with
                          | inl sameB =>
                              exact Or.inr
                                (Or.inr (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) sameB))))
                          | inr rest =>
                              cases rest with
                              | inl sameD =>
                                  exact Or.inr
                                    (Or.inr (Or.inr (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameD)))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameL =>
                                      exact Or.inr
                                        (Or.inr (Or.inr (Or.inr (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm sameRows) sameL))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameE =>
                                          exact Or.inr
                                            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                              (Or.inl
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameE)))))))
                                      | inr sameN =>
                                          exact Or.inr
                                            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                              (Or.inr
                                                (hsame_trans
                                                  (hsame_symm sameRows) sameN))))))) }
        pattern_sound := by
          intro row source
          exact sourceUnary source
        ledger_sound := by
          intro row source
          exact sourceLedger source }
  · exact pkgP

theorem MonotoneCauchyConvergenceRealSealRoute [AskSetup] [PackageSetup]
    {S R O B D L E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonotoneCauchyConvergenceCarrier S R O B D L E H C P N bundle pkg →
      UnaryHistory S ∧
        UnaryHistory R ∧
          UnaryHistory D ∧
            UnaryHistory E ∧
              UnaryHistory O ∧
                UnaryHistory B ∧
                  UnaryHistory L ∧
                    Cont S R D ∧
                      Cont D L E ∧
                        PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg
  intro carrier
  rcases carrier with
    ⟨uS, uR, uO, uB, uD, uL, uE, _uH, _uC, _uP, _uN, routeSRD, routeDLE,
      pkgP, pkgN⟩
  exact
    ⟨uS, uR, uD, uE, uO, uB, uL, routeSRD, routeDLE, pkgP, pkgN⟩

end BEDC.Derived.MonotoneCauchyConvergenceUp
