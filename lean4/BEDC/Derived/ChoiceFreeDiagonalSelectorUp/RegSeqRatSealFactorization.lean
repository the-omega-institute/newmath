import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp.RegSeqRatSealFactorization

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorCarrier_regseqrat_seal_factorization [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName route sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont stream readback route →
        Cont route realSeal sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
              UnaryHistory route ∧ UnaryHistory sealRead ∧ Cont stream readback route ∧
                Cont route realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont PkgSig UnaryHistory
  intro carrier streamReadback routeSeal sealPkg
  obtain ⟨_epsilonUnary, _windowUnary, streamUnary, readbackUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed streamUnary readbackUnary streamReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed routeUnary realSealUnary routeSeal
  exact
    ⟨streamUnary, readbackUnary, realSealUnary, routeUnary, sealUnary, streamReadback,
      routeSeal, provenancePkg, sealPkg⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp.RegSeqRatSealFactorization

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorRegSeqRatSealFactorization [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName windowRead
      witnessRead sealRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont epsilon window windowRead →
        Cont windowRead stream witnessRead →
          Cont witnessRead readback sealRead →
            Cont sealRead realSeal realSealRead →
              SemanticNameCert
                    (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row stream ∨ hsame row readback ∨ hsame row witnessRead ∨
                        hsame row sealRead ∨ hsame row realSeal ∨ hsame row realSealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont windowRead stream witnessRead ∧
                        Cont witnessRead readback sealRead ∧
                          Cont sealRead realSeal realSealRead ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory witnessRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier epsilonWindow windowStream witnessReadback sealReal
  obtain ⟨epsilonUnary, windowUnary, streamUnary, readbackUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary windowUnary epsilonWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowReadUnary streamUnary windowStream
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed witnessReadUnary readbackUnary witnessReadback
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed sealReadUnary realSealUnary sealReal
  have sourceRealSealRead :
      (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row) realSealRead := by
    exact ⟨hsame_refl realSealRead, realSealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row witnessRead ∨
              hsame row sealRead ∨ hsame row realSeal ∨ hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windowRead stream witnessRead ∧
              Cont witnessRead readback sealRead ∧ Cont sealRead realSeal realSealRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSealRead sourceRealSealRead
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, windowStream, witnessReadback, sealReal, provenancePkg⟩
  }
  exact ⟨cert, witnessReadUnary, sealReadUnary, realSealReadUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp
