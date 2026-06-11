import BEDC.Derived.BishopLocatedCompletionBoundaryUp.RegularCauchyExtraction

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryWindowExhaustion [AskSetup] [PackageSetup]
    {stream regseq dyadic regular locatedLimit locatedReal realSeal transport replay
      provenance localName windowRead boundaryRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedCompletionBoundaryCarrier stream regseq dyadic regular locatedLimit
        locatedReal realSeal transport replay provenance localName bundle pkg →
      Cont stream regseq windowRead →
        Cont windowRead dyadic boundaryRead →
          Cont boundaryRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stream ∨ hsame row regseq ∨ hsame row dyadic ∨
                      hsame row regular ∨ hsame row locatedLimit ∨
                        hsame row locatedReal ∨ hsame row realSeal ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont stream regseq windowRead ∧
                      Cont windowRead dyadic boundaryRead ∧
                        Cont boundaryRead realSeal sealRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute boundaryRoute sealRoute sealPkg
  obtain ⟨streamUnary, regseqUnary, dyadicUnary, _regularUnary, _locatedLimitUnary,
    _locatedRealUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _streamRegseqDyadic, _dyadicRegularLocatedLimit,
    _locatedLimitLocatedRealRealSeal, provenancePkg, _localNamePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary regseqUnary windowRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed windowUnary dyadicUnary boundaryRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed boundaryUnary realSealUnary sealRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, windowRoute, boundaryRoute, sealRoute, provenancePkg, sealPkg⟩
    }
  · exact ⟨windowUnary, boundaryUnary, sealUnary⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
