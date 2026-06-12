import BEDC.Derived.FiniteGaugeCoverUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteGaugeCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteGaugeCover_namecert_obligations [AskSetup] [PackageSetup]
    {D C T M Q E U R I H P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory C →
        UnaryHistory T →
          UnaryHistory M →
            Cont D C U →
              Cont T M R →
                Cont U R I →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row U ∨ hsame row R ∨ hsame row I) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row D ∨ hsame row C ∨ hsame row T ∨ hsame row M ∨
                              hsame row Q ∨ hsame row E ∨ hsame row U ∨ hsame row R ∨
                                hsame row I ∨ hsame row H ∨ hsame row P ∨ hsame row N)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont D C U ∧ Cont T M R ∧
                              Cont U R I ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory I := by
  -- BEDC touchpoint anchor: BHist FiniteGaugeCoverUp Cont ProbeBundle Pkg SemanticNameCert
  intro dyadicUnary cellUnary tagUnary meshUnary gaugeRoute tagMeshRoute integralRoute
    provenancePkg namePkg
  have gaugeUnary : UnaryHistory U :=
    unary_cont_closed dyadicUnary cellUnary gaugeRoute
  have tagMeshUnary : UnaryHistory R :=
    unary_cont_closed tagUnary meshUnary tagMeshRoute
  have integralUnary : UnaryHistory I :=
    unary_cont_closed gaugeUnary tagMeshUnary integralRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro I ⟨Or.inr (Or.inr (hsame_refl I)), integralUnary⟩
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
            | inl sameGauge =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameGauge)
            | inr tail =>
                cases tail with
                | inl sameTagMesh =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTagMesh))
                | inr sameIntegral =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameIntegral))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameGauge =>
            right
            right
            right
            right
            right
            right
            left
            exact sameGauge
        | inr tail =>
            cases tail with
            | inl sameTagMesh =>
                right
                right
                right
                right
                right
                right
                right
                left
                exact sameTagMesh
            | inr sameIntegral =>
                right
                right
                right
                right
                right
                right
                right
                right
                left
                exact sameIntegral
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, gaugeRoute, tagMeshRoute, integralRoute, provenancePkg, namePkg⟩
    }
  · exact integralUnary

end BEDC.Derived.FiniteGaugeCoverUp
