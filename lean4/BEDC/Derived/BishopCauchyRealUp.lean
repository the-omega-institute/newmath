import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCauchyRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCauchyRealNameCertObligations [AskSetup] [PackageSetup]
    {regSeq modulus stream dyadic realSeal transport replay provenance name stageRead
      toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory regSeq →
      UnaryHistory modulus →
        UnaryHistory stream →
          UnaryHistory dyadic →
            UnaryHistory realSeal →
              UnaryHistory transport →
                UnaryHistory replay →
                  UnaryHistory provenance →
                    UnaryHistory name →
                      Cont regSeq modulus stageRead →
                        Cont stageRead stream toleranceRead →
                          Cont toleranceRead dyadic sealRead →
                            Cont transport replay provenance →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle name pkg →
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      (hsame row regSeq ∨ hsame row modulus ∨
                                          hsame row stream ∨ hsame row dyadic ∨
                                            hsame row realSeal ∨ hsame row sealRead) ∧
                                        UnaryHistory row)
                                    (fun _row : BHist =>
                                      Cont regSeq modulus stageRead ∧
                                        Cont stageRead stream toleranceRead ∧
                                          Cont toleranceRead dyadic sealRead ∧
                                            Cont transport replay provenance ∧
                                              PkgSig bundle provenance pkg)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro regSeqUnary modulusUnary streamUnary dyadicUnary realSealUnary _transportUnary
    _replayUnary _provenanceUnary _nameUnary regSeqModulus stageStream toleranceDyadic
    transportReplay provenancePkg _namePkg
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed regSeqUnary modulusUnary regSeqModulus
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed stageReadUnary streamUnary stageStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary dyadicUnary toleranceDyadic
  have sourceRegSeq :
      (fun row : BHist =>
        (hsame row regSeq ∨ hsame row modulus ∨ hsame row stream ∨ hsame row dyadic ∨
            hsame row realSeal ∨ hsame row sealRead) ∧
          UnaryHistory row) regSeq := by
    exact ⟨Or.inl (hsame_refl regSeq), regSeqUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro regSeq sourceRegSeq
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
        intro row other sameRows source
        cases source with
        | intro sourceRows sourceUnary =>
            constructor
            · cases sourceRows with
              | inl sameRegSeq =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameRegSeq)
              | inr rest =>
                  cases rest with
                  | inl sameModulus =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameModulus))
                  | inr rest =>
                      cases rest with
                      | inl sameStream =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameStream)))
                      | inr rest =>
                          cases rest with
                          | inl sameDyadic =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameDyadic))))
                          | inr rest =>
                              cases rest with
                              | inl sameRealSeal =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameRealSeal)
                              | inr sameSealRead =>
                                  exact
                                    Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                                      Or.inr
                                        (hsame_trans (hsame_symm sameRows) sameSealRead)
            · exact unary_transport sourceUnary sameRows
    }
    pattern_sound := by
      intro _row _source
      exact ⟨regSeqModulus, stageStream, toleranceDyadic, transportReplay, provenancePkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

end BEDC.Derived.BishopCauchyRealUp
