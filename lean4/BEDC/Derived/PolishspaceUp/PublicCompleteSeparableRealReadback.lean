import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpacePublicCompleteSeparableRealReadback [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead densityRead supportRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont M K completionRead ->
        Cont M D densityRead ->
          Cont completionRead densityRead supportRead ->
            Cont supportRead R publicRead ->
              PkgSig bundle G pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                        hsame row R ∨ hsame row W ∨ hsame row supportRead ∨
                          hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont completionRead densityRead supportRead ∧
                        Cont supportRead R publicRead ∧ PkgSig bundle G pkg ∧
                          PkgSig bundle N pkg)
                    hsame ∧
                    UnaryHistory completionRead ∧ UnaryHistory densityRead ∧
                      UnaryHistory supportRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute densityRoute supportRoute publicRoute carrierPkg localPkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary DUnary densityRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed completionUnary densityUnary supportRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed supportUnary RUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
            hsame row R ∨ hsame row W ∨ hsame row supportRead ∨
              hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont completionRead densityRead supportRead ∧
            Cont supportRead R publicRead ∧ PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
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
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, supportRoute, publicRoute, carrierPkg, localPkg⟩
  }
  exact ⟨cert, completionUnary, densityUnary, supportUnary, publicUnary⟩

end BEDC.Derived.PolishSpaceUp
