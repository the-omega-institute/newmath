import BEDC.Derived.LocatedCauchyFilterUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterNameCertObligations [AskSetup] [PackageSetup]
    {filter basis regular stream readback dyadic locatedTail realSeal transport continuation
      provenance localNameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory filter →
      UnaryHistory basis →
        UnaryHistory stream →
          UnaryHistory readback →
            UnaryHistory dyadic →
              UnaryHistory continuation →
                UnaryHistory provenance →
                  Cont filter basis regular →
                    Cont regular dyadic locatedTail →
                      Cont stream readback realSeal →
                        Cont continuation provenance localNameCert →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localNameCert pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row regular ∨ hsame row locatedTail ∨
                                      hsame row realSeal ∨ hsame row localNameCert) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row filter ∨ hsame row basis ∨ hsame row regular ∨
                                      hsame row stream ∨ hsame row readback ∨ hsame row dyadic ∨
                                        hsame row locatedTail ∨ hsame row realSeal ∨
                                          hsame row localNameCert)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localNameCert pkg)
                                  hsame ∧
                                UnaryHistory regular ∧ UnaryHistory locatedTail ∧
                                  UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro filterUnary basisUnary streamUnary readbackUnary dyadicUnary continuationUnary
    provenanceUnary filterBasisRegular regularDyadicLocated streamReadbackSeal
    continuationProvenanceName provenancePkg localNamePkg
  have _transportSelf : hsame transport transport :=
    hsame_refl transport
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed filterUnary basisUnary filterBasisRegular
  have locatedUnary : UnaryHistory locatedTail :=
    unary_cont_closed regularUnary dyadicUnary regularDyadicLocated
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed streamUnary readbackUnary streamReadbackSeal
  have localNameUnary : UnaryHistory localNameCert :=
    unary_cont_closed continuationUnary provenanceUnary continuationProvenanceName
  have sourceRegular :
      (fun row : BHist =>
        (hsame row regular ∨ hsame row locatedTail ∨ hsame row realSeal ∨
          hsame row localNameCert) ∧ UnaryHistory row)
          regular := by
    exact ⟨Or.inl (hsame_refl regular), regularUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row regular ∨ hsame row locatedTail ∨ hsame row realSeal ∨
              hsame row localNameCert) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row basis ∨ hsame row regular ∨ hsame row stream ∨
              hsame row readback ∨ hsame row dyadic ∨ hsame row locatedTail ∨
                hsame row realSeal ∨ hsame row localNameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localNameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regular sourceRegular
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
          | inl sameRegular =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameRegular)
          | inr rest =>
              cases rest with
              | inl sameLocated =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLocated))
              | inr rest =>
                  cases rest with
                  | inl sameSeal =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)))
                  | inr sameName =>
                      exact Or.inr (Or.inr (Or.inr
                        (hsame_trans (hsame_symm sameRows) sameName)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRegular =>
          exact Or.inr (Or.inr (Or.inl sameRegular))
      | inr rest =>
          cases rest with
          | inl sameLocated =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameLocated))))))
          | inr rest =>
              cases rest with
              | inl sameSeal =>
                  exact Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSeal)))))))
              | inr sameName =>
                  exact Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameName)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, regularUnary, locatedUnary, realSealUnary⟩

end BEDC.Derived.LocatedCauchyFilterUp
