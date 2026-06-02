import BEDC.Derived.OvertRealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OvertRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem OvertRealCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {realSeal interval cover lower upper witness antiEscape transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory realSeal →
      UnaryHistory interval →
        UnaryHistory cover →
          UnaryHistory lower →
            UnaryHistory upper →
              UnaryHistory witness →
                UnaryHistory antiEscape →
                  UnaryHistory transport →
                    UnaryHistory replay →
                      UnaryHistory provenance →
                        UnaryHistory name →
                          Cont realSeal interval cover →
                            Cont cover lower upper →
                              Cont transport replay provenance →
                                PkgSig bundle provenance pkg →
                                  PkgSig bundle name pkg →
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row cover ∨ hsame row lower ∨
                                          hsame row upper ∨ hsame row witness ∨
                                            hsame row antiEscape)
                                      (fun row : BHist =>
                                        hsame row cover ∨ hsame row lower ∨
                                          hsame row upper ∨ hsame row witness ∨
                                            hsame row antiEscape)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                          PkgSig bundle name pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro realUnary intervalUnary coverUnary lowerUnary upperUnary witnessUnary antiEscapeUnary
    _transportUnary _replayUnary _provenanceUnary _nameUnary realInterval _coverLower
    _transportReplay provenancePkg namePkg
  have _routeRows :
      UnaryHistory realSeal ∧ UnaryHistory interval ∧ Cont realSeal interval cover := by
    exact ⟨realUnary, intervalUnary, realInterval⟩
  have sourceCover :
      (fun row : BHist =>
        hsame row cover ∨ hsame row lower ∨ hsame row upper ∨ hsame row witness ∨
          hsame row antiEscape) cover := by
    exact Or.inl (hsame_refl cover)
  exact {
    core := {
      carrier_inhabited := Exists.intro cover sourceCover
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
        cases source with
        | inl sameCover =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameCover)
        | inr rest =>
            cases rest with
            | inl sameLower =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLower))
            | inr rest =>
                cases rest with
                | inl sameUpper =>
                    exact
                      Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameUpper)))
                | inr rest =>
                    cases rest with
                    | inl sameWitness =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameWitness))))
                    | inr sameAntiEscape =>
                        exact
                          Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                            hsame_trans (hsame_symm sameRows) sameAntiEscape
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro row source
      cases source with
      | inl sameCover =>
          exact
            ⟨unary_transport coverUnary (hsame_symm sameCover), provenancePkg, namePkg⟩
      | inr rest =>
          cases rest with
          | inl sameLower =>
              exact
                ⟨unary_transport lowerUnary (hsame_symm sameLower), provenancePkg, namePkg⟩
          | inr rest =>
              cases rest with
              | inl sameUpper =>
                  exact
                    ⟨unary_transport upperUnary (hsame_symm sameUpper), provenancePkg,
                      namePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameWitness =>
                      exact
                        ⟨unary_transport witnessUnary (hsame_symm sameWitness), provenancePkg,
                          namePkg⟩
                  | inr sameAntiEscape =>
                      exact
                        ⟨unary_transport antiEscapeUnary (hsame_symm sameAntiEscape),
                          provenancePkg, namePkg⟩
  }

end BEDC.Derived.OvertRealUp
