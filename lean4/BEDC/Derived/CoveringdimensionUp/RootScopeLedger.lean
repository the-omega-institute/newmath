import BEDC.Derived.CoveringdimensionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootScopeLedger [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead densityRead nerveRead finiteNet metricSource dyadicRead regSeqRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover orderBound rootRead →
        Cont rootRead provenance densityRead →
          Cont densityRead localName nerveRead →
            Cont nerveRead epsilonNet finiteNet →
              Cont finiteNet compactMetric dyadicRead →
                Cont dyadicRead replay regSeqRead →
                  Cont regSeqRead localName realSeal →
                    PkgSig bundle realSeal pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row compactMetric ∨ hsame row epsilonNet ∨
                              hsame row cover ∨ hsame row refinement ∨
                                hsame row orderBound ∨ hsame row densityRead ∨
                                  hsame row nerveRead ∨ hsame row finiteNet ∨
                                    hsame row dyadicRead ∨ hsame row regSeqRead ∨
                                      hsame row realSeal)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont cover orderBound rootRead ∧
                              Cont rootRead provenance densityRead ∧
                                Cont densityRead localName nerveRead ∧
                                  Cont nerveRead epsilonNet finiteNet ∧
                                    Cont finiteNet compactMetric dyadicRead ∧
                                      Cont dyadicRead replay regSeqRead ∧
                                        Cont regSeqRead localName realSeal ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle realSeal pkg)
                          hsame ∧
                        UnaryHistory rootRead ∧ UnaryHistory densityRead ∧
                          UnaryHistory nerveRead ∧ UnaryHistory finiteNet ∧
                            UnaryHistory dyadicRead ∧ UnaryHistory regSeqRead ∧
                              UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverOrderRoot rootProvenanceDensity densityLocalNerve nerveEpsilonFinite
    finiteCompactDyadic dyadicReplayRegSeq regSeqLocalReal realSealPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary orderUnary coverOrderRoot
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed rootUnary provenanceUnary rootProvenanceDensity
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary localNameUnary densityLocalNerve
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed nerveUnary epsilonUnary nerveEpsilonFinite
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed finiteNetUnary compactUnary finiteCompactDyadic
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed dyadicUnary replayUnary dyadicReplayRegSeq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqUnary localNameUnary regSeqLocalReal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, coverOrderRoot, rootProvenanceDensity, densityLocalNerve,
            nerveEpsilonFinite, finiteCompactDyadic, dyadicReplayRegSeq, regSeqLocalReal,
            provenancePkg, realSealPkg⟩
    }
  · exact
      ⟨rootUnary, densityUnary, nerveUnary, finiteNetUnary, dyadicUnary, regSeqUnary,
        realSealUnary⟩

end BEDC.Derived.CoveringdimensionUp
