import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpacePublicReadbackExport [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead densityRead windowRead sealRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K completionRead →
        Cont M D densityRead →
          Cont completionRead densityRead windowRead →
            Cont windowRead W sealRead →
              Cont sealRead R publicRead →
                PkgSig bundle G pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                          hsame row R ∨ hsame row W ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont sealRead R publicRead ∧
                          PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier completionRoute densityRoute windowRoute sealRoute publicRoute
    provenancePkg localNamePkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary DUnary densityRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary densityUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary WUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary RUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
            hsame row R ∨ hsame row W ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont sealRead R publicRead ∧
            PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.PolishspaceUp
