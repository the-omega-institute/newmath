import BEDC.Derived.CauchyEquivalenceSetoidUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidCarrier_obligation_surface [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name classifierRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont s0 r0 classifierRead ->
        Cont test sealRow sealRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont s0 r0 classifierRead ∧
                    Cont test sealRow sealRead ∧ PkgSig bundle classifierRead pkg)
                hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute sealRoute classifierPkg
  obtain ⟨s0Unary, _s1Unary, r0Unary, _r1Unary, _dyadicUnary, testUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed s0Unary r0Unary classifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont s0 r0 classifierRead ∧
              Cont test sealRow sealRead ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro classifierRead ⟨hsame_refl classifierRead, classifierUnary⟩
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
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, classifierRoute, sealRoute, classifierPkg⟩
  }
  exact ⟨cert, classifierUnary, sealReadUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
