import BEDC.Derived.BoundedFunctionFamilyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BoundedFunctionFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedFunctionFamilySupNormNonescape [AskSetup] [PackageSetup]
    {source target index maps pointBounds supNorm transport replay provenance localName
      normRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedFunctionFamilyCarrier source target index maps pointBounds supNorm transport replay
        provenance localName bundle pkg ->
      Cont maps pointBounds normRead ->
        Cont normRead supNorm boundedRead ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row index ∨
                    hsame row maps ∨ hsame row pointBounds ∨ hsame row supNorm ∨
                      hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                        hsame row localName ∨ hsame row normRead ∨
                          hsame row boundedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont maps pointBounds normRead ∧
                    Cont normRead supNorm boundedRead ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory normRead ∧ UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier normRoute boundedRoute provenancePkg
  obtain ⟨_sourceUnary, _targetUnary, _indexUnary, mapsUnary, pointBoundsUnary,
    supNormUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _sourceMapsReplay, _mapsPointBoundsSupNorm, _transportReplayProvenance,
    _carrierProvenancePkg, _localNamePkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed mapsUnary pointBoundsUnary normRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed normUnary supNormUnary boundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row index ∨ hsame row maps ∨
              hsame row pointBounds ∨ hsame row supNorm ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row normRead ∨ hsame row boundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont maps pointBounds normRead ∧
              Cont normRead supNorm boundedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundedRead ⟨hsame_refl boundedRead, boundedUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, normRoute, boundedRoute, provenancePkg⟩
  }
  exact ⟨cert, normUnary, boundedUnary⟩

end BEDC.Derived.BoundedFunctionFamilyUp
