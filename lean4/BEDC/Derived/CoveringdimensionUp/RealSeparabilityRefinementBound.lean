import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringDimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CoveringdimensionUp

theorem CoveringDimensionRealSeparabilityRefinementBound [AskSetup] [PackageSetup]
    {K E C R O L H T P N densityRead refinementRead orderRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont K E densityRead →
        Cont densityRead C refinementRead →
          Cont refinementRead R orderRead →
            Cont orderRead L ledgerRead →
              Cont ledgerRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                          hsame row O ∨ hsame row L ∨ hsame row N ∨
                            hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K E densityRead ∧
                          Cont densityRead C refinementRead ∧
                            Cont refinementRead R orderRead ∧
                              Cont orderRead L ledgerRead ∧
                                Cont ledgerRead N namedRead ∧
                                  PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute refinementRoute orderRoute ledgerRoute namedRoute namedPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed compactUnary epsilonUnary densityRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed densityUnary coverUnary refinementRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementReadUnary refinementUnary orderRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed orderReadUnary lebesgueUnary ledgerRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
              hsame row L ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K E densityRead ∧
              Cont densityRead C refinementRead ∧ Cont refinementRead R orderRead ∧
                Cont orderRead L ledgerRead ∧ Cont ledgerRead N namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        ⟨source.right, densityRoute, refinementRoute, orderRoute, ledgerRoute,
          namedRoute, namedPkg⟩
  }
  exact ⟨cert, namedReadUnary⟩

end BEDC.Derived.CoveringDimensionUp
