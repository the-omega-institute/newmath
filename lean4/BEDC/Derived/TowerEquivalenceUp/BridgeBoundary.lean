import BEDC.Derived.TowerEquivalenceUp.NameCertObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TowerEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TowerEquivalenceBridgeBoundary [AskSetup] [PackageSetup]
    {ledger descent objectivity transport provenance name bridgeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory ledger ->
      UnaryHistory descent ->
        UnaryHistory objectivity ->
          UnaryHistory transport ->
            UnaryHistory provenance ->
              UnaryHistory name ->
                Cont ledger descent bridgeRead ->
                  Cont bridgeRead transport namedRead ->
                    PkgSig bundle namedRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row ledger ∨ hsame row descent ∨ hsame row objectivity ∨
                              hsame row transport ∨ hsame row provenance ∨ hsame row name ∨
                                hsame row bridgeRead ∨ hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont ledger descent bridgeRead ∧
                              Cont bridgeRead transport namedRead ∧
                                PkgSig bundle namedRead pkg)
                          hsame ∧
                        UnaryHistory bridgeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro unaryLedger unaryDescent _unaryObjectivity unaryTransport _unaryProvenance
    _unaryName bridgeRoute namedRoute namedPkg
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed unaryLedger unaryDescent bridgeRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed bridgeUnary unaryTransport namedRoute
  have sourceAtNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ledger ∨ hsame row descent ∨ hsame row objectivity ∨
              hsame row transport ∨ hsame row provenance ∨ hsame row name ∨
                hsame row bridgeRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ledger descent bridgeRead ∧
              Cont bridgeRead transport namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceAtNamed
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
      right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, bridgeUnary, namedUnary⟩

end BEDC.Derived.TowerEquivalenceUp
