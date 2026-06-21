import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp.ObligationCarrier

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorCarrier_obligation_carrier [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            Cont sealRead localName namedRead →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row namedRead ∧ UnaryHistory row ∧ PkgSig bundle localName pkg)
                    (fun row : BHist =>
                      hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
                        hsame row readback ∨ hsame row realSeal ∨ hsame row provenance ∨
                          hsame row localName ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont epsilon window windowRead ∧
                        Cont windowRead stream witnessRead ∧
                          Cont witnessRead readback sealRead ∧
                            Cont sealRead localName namedRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier epsilonWindow windowStream witnessReadback sealLocalName localNamePkg
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, _realSealUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary localNameUnary sealLocalName
  have sourceNamed :
      (fun row : BHist =>
        hsame row namedRead ∧ UnaryHistory row ∧ PkgSig bundle localName pkg) namedRead := by
    exact ⟨hsame_refl namedRead, namedReadUnary, localNamePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row namedRead ∧ UnaryHistory row ∧ PkgSig bundle localName pkg)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
              hsame row readback ∨ hsame row realSeal ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilon window windowRead ∧
              Cont windowRead stream witnessRead ∧ Cont witnessRead readback sealRead ∧
                Cont sealRead localName namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.left, epsilonWindow, windowStream, witnessReadback,
        sealLocalName, provenancePkg, sourceRow.right.right⟩
  }
  exact ⟨cert, namedReadUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp.ObligationCarrier
