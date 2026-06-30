import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationBudgetCarrier_candidate_sn_boundary [AskSetup] [PackageSetup]
    {term candidate evidence normalization adequacy replay refusal transport routes provenance
      localName snRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory term →
      UnaryHistory candidate →
        UnaryHistory evidence →
          UnaryHistory normalization →
            UnaryHistory adequacy →
              UnaryHistory refusal →
                Cont term candidate evidence →
                  Cont evidence normalization snRead →
                    Cont snRead adequacy replay →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle snRead pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row snRead ∨ hsame row refusal) ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row candidate ∨ hsame row evidence ∨
                                  hsame row snRead ∨ hsame row refusal)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle snRead pkg)
                              hsame ∧
                            UnaryHistory snRead ∧ UnaryHistory replay ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _termUnary _candidateUnary evidenceUnary normalizationUnary adequacyUnary refusalUnary
    _candidateRoute snRoute replayRoute provenancePkg snPkg
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed evidenceUnary normalizationUnary snRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed snUnary adequacyUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row snRead ∨ hsame row refusal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row evidence ∨ hsame row snRead ∨ hsame row refusal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle snRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro snRead ⟨Or.inl (hsame_refl snRead), snUnary⟩
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
            | inl sameSN =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSN)
            | inr sameRefusal =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameSN =>
            exact Or.inr (Or.inr (Or.inl sameSN))
        | inr sameRefusal =>
            exact Or.inr (Or.inr (Or.inr sameRefusal))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, snPkg⟩
    }
  exact ⟨cert, snUnary, replayUnary, provenancePkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
