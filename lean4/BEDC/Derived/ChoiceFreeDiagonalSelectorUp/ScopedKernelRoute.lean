import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorScopedKernelRoute [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead transportRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            Cont sealRead transport transportRead →
              Cont transportRead localName namedRead →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
                          hsame row readback ∨ hsame row realSeal ∨ hsame row transport ∨
                            hsame row replay ∨ hsame row provenance ∨
                              hsame row localName ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont epsilon window windowRead ∧
                          Cont windowRead stream witnessRead ∧
                            Cont witnessRead readback sealRead ∧
                              Cont sealRead transport transportRead ∧
                                Cont transportRead localName namedRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory witnessRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory transportRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier epsilonWindow windowStream witnessReadback sealTransport transportLocal
    localNamePkg
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, _realSealUnary,
    transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed sealReadUnary transportUnary sealTransport
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed transportReadUnary localNameUnary transportLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
              hsame row readback ∨ hsame row realSeal ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilon window windowRead ∧
              Cont windowRead stream witnessRead ∧ Cont witnessRead readback sealRead ∧
                Cont sealRead transport transportRead ∧
                  Cont transportRead localName namedRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, epsilonWindow, windowStream, witnessReadback, sealTransport,
          transportLocal, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, windowReadUnary, witnessReadUnary, sealReadUnary, transportReadUnary,
      namedReadUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp
