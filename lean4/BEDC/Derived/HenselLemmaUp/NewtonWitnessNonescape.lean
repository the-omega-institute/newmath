import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HenselLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HenselLemmaNewtonWitnessNonescape [AskSetup] [PackageSetup]
    {K R F P A V N E T C Q L separationRead correctionRead nonescapeRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V →
      UnaryHistory N →
        UnaryHistory E →
          UnaryHistory C →
            Cont V N correctionRead →
              Cont correctionRead E nonescapeRead →
                Cont nonescapeRead C namedRead →
                  PkgSig bundle Q pkg →
                    PkgSig bundle L pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row correctionRead ∨ hsame row nonescapeRead ∨
                              hsame row namedRead) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row R ∨ hsame row F ∨
                              hsame row P ∨ hsame row A ∨ hsame row V ∨
                                hsame row N ∨ hsame row E ∨ hsame row correctionRead ∨
                                  hsame row nonescapeRead ∨ hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont V N correctionRead ∧
                              Cont correctionRead E nonescapeRead ∧
                                Cont nonescapeRead C namedRead ∧ PkgSig bundle Q pkg ∧
                                  PkgSig bundle L pkg)
                          hsame ∧ UnaryHistory correctionRead ∧ UnaryHistory nonescapeRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryV unaryN unaryE unaryC correctionStep nonescapeStep namedStep provenancePkg
    localPkg
  have correctionUnary : UnaryHistory correctionRead :=
    unary_cont_closed unaryV unaryN correctionStep
  have nonescapeUnary : UnaryHistory nonescapeRead :=
    unary_cont_closed correctionUnary unaryE nonescapeStep
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed nonescapeUnary unaryC namedStep
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead
            ⟨Or.inr (Or.inr (hsame_refl namedRead)), namedUnary⟩
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
          constructor
          · cases source.left with
            | inl sameCorrection =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameCorrection)
            | inr rest =>
                cases rest with
                | inl sameNonescape =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNonescape))
                | inr sameNamed =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameNamed))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameCorrection =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inl sameCorrection))))))))
        | inr rest =>
            cases rest with
            | inl sameNonescape =>
                exact
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (Or.inl sameNonescape)))))))))
            | inr sameNamed =>
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
                                    (Or.inr sameNamed)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, correctionStep, nonescapeStep, namedStep, provenancePkg,
            localPkg⟩
    }
  · exact ⟨correctionUnary, nonescapeUnary, namedUnary⟩

end BEDC.Derived.HenselLemmaUp
