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

theorem CauchyEquivalenceSetoidPsameRealClassifierBridge [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead
      realClassifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont test sealRow sealRead ->
        Cont sealRead replay equalityRead ->
          Cont equalityRead name realClassifierRead ->
            PkgSig bundle equalityRead pkg ->
              PkgSig bundle realClassifierRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row realClassifierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sealRead ∨ hsame row equalityRead ∨
                        hsame row realClassifierRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont test sealRow sealRead ∧
                        Cont sealRead replay equalityRead ∧
                          Cont equalityRead name realClassifierRead ∧
                            PkgSig bundle realClassifierRead pkg)
                    hsame ∧
                  UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧
                    UnaryHistory realClassifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute equalityRoute realClassifierRoute _equalityPkg realClassifierPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary, sealUnary,
    _transportUnary, replayUnary, _provenanceUnary, nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed sealReadUnary replayUnary equalityRoute
  have realClassifierUnary : UnaryHistory realClassifierRead :=
    unary_cont_closed equalityReadUnary nameUnary realClassifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realClassifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealRead ∨ hsame row equalityRead ∨ hsame row realClassifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead replay equalityRead ∧
                Cont equalityRead name realClassifierRead ∧
                  PkgSig bundle realClassifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realClassifierRead
          ⟨hsame_refl realClassifierRead, realClassifierUnary⟩
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
      exact Or.inr (Or.inr sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sealRoute, equalityRoute, realClassifierRoute,
          realClassifierPkg⟩
  }
  exact ⟨cert, sealReadUnary, equalityReadUnary, realClassifierUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
